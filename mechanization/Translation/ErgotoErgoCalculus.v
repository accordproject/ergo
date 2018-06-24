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
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoSugar.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgotoErgoCalculus.

  (** Translate an Ergo statement to an Ergo expression *)

  Fixpoint ergo_stmt_to_expr (s:ergo_stmt) : ergoc_expr :=
    let loc := stmt_loc s in
    match stmt_desc s with
    | SReturn e =>
      ESuccess loc (mk_result
                      loc
                      e
                      (mk_expr loc (EVar local_state))
                      (mk_expr loc (EVar local_emit)))
    | SFunReturn e =>
      e (* Returning from a function does not have state or emit, just the result *)
    | SThrow e =>
      EError loc e
    | SCallClause fname el =>
      mk_expr
        loc
        (ECallFun
           fname
           (mk_expr loc EThisContract
              ::mk_expr loc (EVar local_state)
              ::mk_expr loc (EVar local_emit)
              ::el))
    | SSetState e1 s2 =>
      set_state loc e1 (ergo_stmt_to_expr s2)
    | SEmit e1 s2 =>
      push_emit loc e1 (ergo_stmt_to_expr s2)
    | SLet vname vtype e1 s2 =>
      mk_expr
        loc
        (ELet vname vtype
              e1
              (ergo_stmt_to_expr s2))
    | SIf e1 s2 s3 =>
      mk_expr
        loc
        (EIf e1
             (ergo_stmt_to_expr s2)
             (ergo_stmt_to_expr s3))
    | SEnforce e1 None s3 =>
      mk_expr
        loc
        (EIf (mk_expr loc (EUnaryOp OpNeg e1))
             (EError loc (mk_expr loc (EConst enforce_error_content)))
             (ergo_stmt_to_expr s3))
    | SEnforce e1 (Some s2) s3 =>
      mk_expr
        loc
        (EIf (mk_expr loc (EUnaryOp OpNeg e1))
             (ergo_stmt_to_expr s2)
             (ergo_stmt_to_expr s3))
    | SMatch e sl sdefault =>
      mk_expr
        loc
        (EMatch e
                (map (fun xy => (fst xy, (ergo_stmt_to_expr (snd xy)))) sl)
                (ergo_stmt_to_expr sdefault))
    end.

  Definition ergoc_expr_top (loc:location) (e:ergoc_expr) : ergoc_expr :=
    mk_expr loc (ELet local_state None (mk_expr loc (EVar this_state))
                      (mk_expr loc (ELet local_emit None (mk_expr loc (EVar this_emit)) e))).

  (** Translate a clause to clause+calculus *)

  Definition clause_to_calculus (tem:ergo_type) (sta:option ergo_type) (c:ergo_clause) : ergoc_function :=
    let loc := c.(clause_location) in
    let response_type := c.(clause_lambda).(lambda_output) in
    let emit_type := lift_default_emits_type loc c.(clause_lambda).(lambda_emits) in
    let state_type :=  lift_default_state_type loc sta in
    let success_type := mk_success_type loc response_type state_type emit_type in
    let throw_type := lift_default_throws_type loc c.(clause_lambda).(lambda_throws) in
    let error_type := mk_error_type loc throw_type in
    mkFuncC
      c.(clause_name)
      (mkLambdaC
         ((this_contract, tem)
            ::(this_state, state_type)
            ::(this_emit,mk_type loc (ErgoTypeArray emit_type))
            ::c.(clause_lambda).(lambda_params))
         (mk_output_type loc success_type error_type)
         (ergoc_expr_top loc (ergo_stmt_to_expr c.(clause_lambda).(lambda_body)))).

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
    match decl_desc s with
    | DType ergo_type => None
    | DStmt s => Some (ECExpr (ergo_stmt_to_expr s))
    | DConstant v e => Some (ECConstant v e)
    | DFunc f => Some (ECFunc (function_to_calculus f))
    | DContract c => Some (ECContract (contract_to_calculus c))
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
             dummy_location
             (mkLambda (("rate"%string, mk_type dummy_location ErgoTypeDouble)::nil)
                       (mk_type dummy_location ErgoTypeAny)
                       None
                       None
                       (mk_stmt dummy_location
                                (SReturn (mk_expr dummy_location (EConst (dfloat float_one)))))).
    Definition cl1 :=
      mkClause "volumediscount"
             dummy_location
               (mkLambda (("request"%string, mk_type dummy_location (ErgoTypeClassRef default_request_type))::nil)
                         (mk_type dummy_location ErgoTypeAny)
                         None
                         None
                         (mk_stmt
                            dummy_location
                            (SReturn
                               (mk_expr
                                  dummy_location
                                  (ECallFun "addFee"
                                            (mk_expr dummy_location (EConst (dfloat float_zero))::nil)))))).
    Definition co1 : ergo_contract :=
      mkContract
        "VolumeDiscount"
        dummy_location
        (mk_type dummy_location
                 (ErgoTypeClassRef (AbsoluteRef "TemplateModel"%string)))
        None
        (cl1::nil).

    Definition dl : list ergo_declaration :=
      ((mk_decl dummy_location (DFunc f1))
         :: (mk_decl dummy_location (DContract co1))::nil).

    (* Eval vm_compute in (declarations_calculus dl). *)
  End Examples.

  (** Translate a module to a module+calculus *)
  Definition module_to_calculus (p:ergo_module) : ergoc_module :=
    mkModuleC
      p.(module_namespace)
      (declarations_calculus p.(module_declarations)).

End ErgotoErgoCalculus.

