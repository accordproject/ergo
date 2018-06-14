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
    | None => CTOClassRef default_emits
    end.
  
  Definition clause_to_calculus (c:ergo_clause) : ergoc_clause :=
    mkClauseC
      c.(clause_name)
      (mkLambdaC
         ((this_contract,CTOAny)
            ::(this_state,CTOAny)
            ::(this_emit,CTOArray CTOAny)
            ::c.(clause_lambda).(lambda_params))
         c.(clause_lambda).(lambda_output)
         c.(clause_lambda).(lambda_throws)
         (Some (default_emits_in_clause c.(clause_lambda).(lambda_emits)))
         (ergoc_expr_top (ergo_stmt_to_expr c.(clause_lambda).(lambda_body)))).

  (** Translate a function to function+calculus *)
  Definition function_to_calculus (f:ergo_function) : ergoc_function :=
    mkFuncC
      f.(function_name)
      (mkLambdaC
         f.(function_lambda).(lambda_params)
         f.(function_lambda).(lambda_output)
         f.(function_lambda).(lambda_throws)
         f.(function_lambda).(lambda_emits)
         (ergo_stmt_to_expr f.(function_lambda).(lambda_body))).

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the comp_context *)

  Definition contract_to_calculus (c:ergo_contract) : ergoc_contract :=
    let clauses := map clause_to_calculus c.(contract_clauses) in
    mkContractC
      c.(contract_name)
      c.(contract_template)
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

  (** Translate a package to a package+calculus *)
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
               (mkLambda (("request"%string, CTOClassRef "Request")::nil)
                         CTOAny
                         None
                         None
                         (SReturn (ECallFun "addFee" ((EConst (dfloat float_zero))::nil)))).
    Definition co1 :=
      mkContract
        "VolumeDiscount"
        "TemplateModel"
        (cl1::nil).

    Definition dl : list ergo_declaration := (EFunc f1::EContract co1::nil).

    (* Eval vm_compute in (declarations_calculus dl). *)
  End Examples.

  (** Translate a package to a package+calculus *)
  Definition package_to_calculus (p:ergo_package) : ergoc_package :=
    mkPackageC
      p.(package_namespace)
      (declarations_calculus p.(package_declarations)).

End ErgotoErgoCalculus.

