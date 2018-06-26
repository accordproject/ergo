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
  Fixpoint ergo_stmt_to_expr (s:laergo_stmt) : ergoc_expr :=
    match s with
    | SReturn loc e =>
      ESuccess loc (mk_result
                      loc
                      e
                      (EVar loc local_state)
                      (EVar loc local_emit))
    | SFunReturn loc e =>
      e (* Returning from a function does not have state or emit, just the result *)
    | SThrow loc e =>
      EError loc e
    | SCallClause loc fname el =>
      ECallFun loc
               fname
               ((EThisContract loc)
                        ::(EVar loc local_state)
                        ::(EVar loc local_emit)
                        ::el)
    | SSetState loc e1 s2 =>
      set_state loc e1 (ergo_stmt_to_expr s2)
    | SEmit loc e1 s2 =>
      push_emit loc e1 (ergo_stmt_to_expr s2)
    | SLet loc vname vtype e1 s2 =>
      ELet loc vname vtype
           e1
           (ergo_stmt_to_expr s2)
    | SIf loc e1 s2 s3 =>
      EIf loc e1
          (ergo_stmt_to_expr s2)
          (ergo_stmt_to_expr s3)
    | SEnforce loc e1 None s3 =>
      EIf loc (EUnaryOp loc OpNeg e1)
          (EError loc (EConst loc enforce_error_content))
          (ergo_stmt_to_expr s3)
    | SEnforce loc e1 (Some s2) s3 =>
      EIf loc
          (EUnaryOp loc OpNeg e1)
          (ergo_stmt_to_expr s2)
          (ergo_stmt_to_expr s3)
    | SMatch loc e sl sdefault =>
      EMatch loc e
             (map (fun xy => (fst xy, (ergo_stmt_to_expr (snd xy)))) sl)
             (ergo_stmt_to_expr sdefault)
    end.

  Definition ergoc_expr_top (loc:location) (e:ergoc_expr) : ergoc_expr :=
    ELet loc
         local_state
         None
         (EVar loc this_state)
         (ELet loc local_emit None (EVar loc this_emit) e).

  (** Translate a clause to clause+calculus *)

  Definition clause_to_calculus (tem:laergo_type) (sta:option laergo_type) (c:laergo_clause) : ergoc_function :=
    let loc := c.(clause_annot) in
    let response_type := c.(clause_sig).(type_signature_output) in
    let emit_type := lift_default_emits_type loc c.(clause_sig).(type_signature_emits) in
    let state_type :=  lift_default_state_type loc sta in
    let success_type := mk_success_type loc response_type state_type emit_type in
    let throw_type := lift_default_throws_type loc c.(clause_sig).(type_signature_throws) in
    let error_type := mk_error_type loc throw_type in
    mkFuncC
      c.(clause_annot)
      c.(clause_name)
      (mkLambdaC
         ((this_contract, tem)
            ::(this_state, state_type)
            ::(this_emit, ErgoTypeArray loc emit_type)
            ::c.(clause_sig).(type_signature_params))
         (mk_output_type loc success_type error_type)
         (ergoc_expr_top loc (ergo_stmt_to_expr c.(clause_body)))).

  (** Translate a function to function+calculus *)
  Definition function_to_calculus (f:laergo_function) : ergoc_function :=
    mkFuncC
      f.(function_annot)
      f.(function_name)
      (mkLambdaC
         f.(function_sig).(type_signature_params)
         f.(function_sig).(type_signature_output)
         (ergo_stmt_to_expr f.(function_body))).

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the comp_context *)

  Definition contract_to_calculus (c:laergo_contract) : ergoc_contract :=
    let clauses := map (clause_to_calculus c.(contract_template) c.(contract_state)) c.(contract_clauses) in
    mkContractC
      c.(contract_annot)
      c.(contract_name)
      clauses.

  (** Translate a statement to a statement+calculus *)
  Definition declaration_to_calculus (s:laergo_declaration) : option (ergoc_declaration) :=
    match s with
    | DType loc ergo_type => None
    | DStmt loc s => Some (DCExpr loc (ergo_stmt_to_expr s))
    | DConstant loc v e => Some (DCConstant loc v e)
    | DFunc loc f => Some (DCFunc loc (function_to_calculus f))
    | DContract loc c => Some (DCContract loc (contract_to_calculus c))
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
    Definition f1 : laergo_function :=
      mkFunc dummy_location
             "addFee"%string
             (mkErgoTypeSignature
                dummy_location
                (("rate"%string, ErgoTypeDouble dummy_location)::nil)
                (ErgoTypeAny dummy_location)
                None
                None)
             (SReturn dummy_location (EConst dummy_location (dfloat float_one))).
    Definition cl1 : laergo_clause :=
      mkClause dummy_location
               "volumediscount"%string
               (mkErgoTypeSignature
                  dummy_location
                  (("request"%string, ErgoTypeClassRef dummy_location default_request_absolute_name)::nil)
                  (ErgoTypeAny dummy_location)
                  None
                  None)
               (SReturn
                  dummy_location
                  (ECallFun dummy_location "addFee"
                            (EConst dummy_location (dfloat float_zero)::nil))).
    Definition co1 : laergo_contract :=
      mkContract
        dummy_location
        "VolumeDiscount"%string
        (ErgoTypeClassRef dummy_location "TemplateModel"%string)
        None
        (cl1::nil).

    Definition dl : list laergo_declaration :=
      (DFunc dummy_location f1)
        :: (DContract dummy_location co1)
        :: nil.

    (* Compute (declarations_calculus dl). *)
  End Examples.

  (** Translate a module to a module+calculus *)
  Definition ergo_module_to_calculus (p:laergo_module) : ergoc_module :=
    mkModuleC
      p.(module_annot)
      p.(module_namespace)
      (declarations_calculus p.(module_declarations)).

  Definition ergo_modules_to_calculus (pl:list laergo_module) : list ergoc_module :=
    map ergo_module_to_calculus pl.

End ErgotoErgoCalculus.

