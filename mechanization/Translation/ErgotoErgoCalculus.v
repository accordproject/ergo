(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** Translates contract logic to calculus *)

Require Import String.
Require Import List.

Require Import Qcert.Utils.Utils.
Require Import Qcert.NNRC.NNRCRuntime.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoSugar.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgotoErgoCalculus.

  (** Translate an Ergo statement to an Ergo expression *)

  Fixpoint ergo_stmt_to_expr (s:ergo_stmt) : ergoc_expr :=
    match s with
    | SReturn e =>
      ESuccess (mk_result e (EVar local_state) (EVar local_emit))
    | SFunReturn e =>
      e (* Returning from a function does not have state or emit, just the result *)
    | SThrow e =>
      EError e
    | SCallClause fname el =>
      ECallFun fname (EThisContract::(EVar local_state)::(EVar local_emit)::el)
    | SSetState e1 s2 =>
      set_state e1 (ergo_stmt_to_expr s2)
    | SEmit e1 s2 =>
      push_emit e1 (ergo_stmt_to_expr s2)
    | SLet vname vtype e1 s2 =>
      ELet vname vtype
           e1
           (ergo_stmt_to_expr s2)
    | SIf e1 s2 s3 =>
      EIf e1
          (ergo_stmt_to_expr s2)
          (ergo_stmt_to_expr s3)
    | SEnforce e1 None s3 =>
      EIf (EUnaryOp OpNeg e1)
          (EError (EConst enforce_error_content))
          (ergo_stmt_to_expr s3)
    | SEnforce e1 (Some s2) s3 =>
      EIf (EUnaryOp OpNeg e1)
          (ergo_stmt_to_expr s2)
          (ergo_stmt_to_expr s3)
    | SMatch e sl sdefault =>
      EMatch e
             (map (fun xy => (fst xy, (ergo_stmt_to_expr (snd xy)))) sl)
             (ergo_stmt_to_expr sdefault)
    end.

  Definition ergoc_expr_top (e:ergoc_expr) : ergoc_expr :=
    ELet local_state None (EVar this_state)
         (ELet local_emit None (EVar this_emit) e).

  (** Translate a clause to clause+calculus *)

  Definition default_emits_in_clause (emits:option cto_type) : cto_type :=
    match emits with
    | Some e => e
    | None => CTOClassRef default_event_type
    end.

  Definition default_state_in_clause (state:option cto_type) : cto_type :=
    match state with
    | Some e => e
    | None => CTOClassRef default_state_type
    end.

  Definition default_throws_in_clause (emits:option cto_type) : cto_type :=
    match emits with
    | Some e => e
    | None => CTOClassRef default_throws_type
    end.

  Definition mk_success_type (response_type state_type emit_type: cto_type) :=
    CTORecord (("response",response_type)::("state",state_type)::("emit",emit_type)::nil)%string.
  Definition mk_error_type (throw_type: cto_type) :=
    throw_type.
  Definition mk_output_type (success_type error_type: cto_type) :=
    CTOSum success_type error_type.

  Definition clause_to_calculus (tem:cto_type) (sta:option cto_type) (c:ergo_clause) : ergoc_function :=
    let response_type := c.(clause_lambda).(lambda_output) in
    let emit_type := default_emits_in_clause c.(clause_lambda).(lambda_emits) in
    let state_type :=  default_state_in_clause sta in
    let success_type := mk_success_type response_type state_type emit_type in
    let throw_type := default_throws_in_clause c.(clause_lambda).(lambda_throws) in
    let error_type := mk_error_type throw_type in
    mkFuncC
      c.(clause_name)
      (mkLambdaC
         ((this_contract, tem)
            ::(this_state, state_type)
            ::(this_emit,CTOArray emit_type)
            ::c.(clause_lambda).(lambda_params))
         (mk_output_type success_type error_type)
         (ergoc_expr_top (ergo_stmt_to_expr c.(clause_lambda).(lambda_body)))).

  (** Translate a function to function+calculus *)
  Definition function_to_calculus (f:ergo_function) : ergoc_function :=
    mkFuncC
      f.(function_name)
      (mkLambdaC
         f.(function_lambda).(lambda_params)
         f.(function_lambda).(lambda_output)
         (ergo_stmt_to_expr f.(function_lambda).(lambda_body))).

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the comp_context *)

  Definition contract_to_calculus (c:ergo_contract) : ergoc_contract :=
    let clauses := map (clause_to_calculus c.(contract_template) c.(contract_state)) c.(contract_clauses) in
    mkContractC
      c.(contract_name)
      clauses.

  (** Translate a statement to a statement+calculus *)
  Definition declaration_to_calculus (s:ergo_declaration) : option (ergoc_declaration) :=
    match s with
    | EType cto_type => None
    | EExpr e => Some (ECExpr e)
    | EGlobal v e => Some (ECGlobal v e)
    | EImport s => None
    | EFunc f => Some (ECFunc (function_to_calculus f))
    | EContract c => Some (ECContract (contract_to_calculus c))
    end.

  (** Translate a module to a module+calculus *)
  Definition declarations_calculus (dl:list ergo_declaration) : list ergoc_declaration :=
    let proc_one
          (d:ergo_declaration)
          (acc:list ergoc_declaration)
        : list ergoc_declaration :=
        match declaration_to_calculus d with
        | None => acc
        | Some edecl => edecl :: acc
        end
    in
    List.fold_right proc_one nil dl.

  Section Examples.
    Definition f1 :=
      mkFunc "addFee"
             (mkLambda (("rate"%string, CTODouble)::nil)
                       CTOAny
                       None
                       None
                       (SReturn (EConst (dfloat float_one)))).
    Definition cl1 :=
      mkClause "volumediscount"
               (mkLambda (("request"%string, CTOClassRef default_request_type)::nil)
                         CTOAny
                         None
                         None
                         (SReturn (ECallFun "addFee" ((EConst (dfloat float_zero))::nil)))).
    Definition co1 : ergo_contract :=
      mkContract
        "VolumeDiscount"
        (CTOClassRef (AbsoluteRef "TemplateModel"%string))
        None
        (cl1::nil).

    Definition dl : list ergo_declaration := (EFunc f1::EContract co1::nil).

    (* Eval vm_compute in (declarations_calculus dl). *)
  End Examples.

  (** Translate a module to a module+calculus *)
  Definition module_to_calculus (p:ergo_module) : ergoc_module :=
    mkModuleC
      p.(module_namespace)
      (declarations_calculus p.(module_declarations)).

End ErgotoErgoCalculus.

