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
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculusSugar.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgotoErgoCalculus.

  Section TranslationContext.
    Record translation_context :=
      mkTransContext {
          trans_ctxt_current_contract : option string;
          trans_ctxt_current_clause : option string;
        }.

    Definition initial_translation_context :=
      mkTransContext None None.

    Definition set_current_contract (ctxt:translation_context) (cname:string) : translation_context :=
      mkTransContext
        (Some cname)
        ctxt.(trans_ctxt_current_clause).
  
    Definition set_current_clause (ctxt:translation_context) (cname:string) : translation_context :=
      mkTransContext
        ctxt.(trans_ctxt_current_contract)
        (Some cname).

  End TranslationContext.

  (** Translate Ergo expression to calculus *)
  Fixpoint ergo_expr_to_ergoc_expr (ctxt:translation_context) (e:laergo_expr) : eresult ergoc_expr :=
    match e with
    | EThisContract prov =>
      match ctxt.(trans_ctxt_current_contract) with
      | None => not_in_contract_error prov
      | Some _ => esuccess (thisContract prov)
      end
    | EThisClause prov => 
      match ctxt.(trans_ctxt_current_clause) with
      | None => not_in_clause_error prov
      | Some clause_name =>
        esuccess (thisClause prov clause_name)
      end
    | EThisState prov =>
      esuccess (thisState prov)
    | EVar prov v =>
      esuccess (EVar prov v)
    | EConst prov d =>
      esuccess (EConst prov d)
    | EArray prov el =>
      let init_el := esuccess nil in
      let proc_one (e:laergo_expr) (acc:eresult (list ergoc_expr)) : eresult (list ergoc_expr) :=
          elift2
            cons
            (ergo_expr_to_ergoc_expr ctxt e)
            acc
      in
      elift (EArray prov) (fold_right proc_one init_el el)
    | EUnaryOp prov u e =>
      elift
        (EUnaryOp prov u)
        (ergo_expr_to_ergoc_expr ctxt e)
    | EBinaryOp prov b e1 e2 =>
      elift2 (EBinaryOp prov b)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_expr_to_ergoc_expr ctxt e2)
    | EIf prov e1 e2 e3 =>
      elift3 (EIf prov)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_expr_to_ergoc_expr ctxt e2)
             (ergo_expr_to_ergoc_expr ctxt e3)
    | ELet prov v ta e1 e2 =>
      elift2 (ELet prov v ta)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_expr_to_ergoc_expr ctxt e2)
    | ENew prov cr el =>
      let init_rec := esuccess nil in
      let proc_one (att:string * laergo_expr) (acc:eresult (list (string * ergoc_expr))) :=
          let attname := fst att in
          let e := ergo_expr_to_ergoc_expr ctxt (snd att) in
          elift2 (fun e => fun acc => (attname,e)::acc) e acc
      in
      elift (ENew prov cr) (fold_right proc_one init_rec el)
    | ERecord prov el =>
      let init_rec := esuccess nil in
      let proc_one (att:string * laergo_expr) (acc:eresult (list (string * ergoc_expr))) :=
          let attname := fst att in
          let e := ergo_expr_to_ergoc_expr ctxt (snd att) in
          elift2 (fun e => fun acc => (attname,e)::acc) e acc
      in
      elift (ERecord prov) (fold_right proc_one init_rec el)
    | ECallFun prov fname el =>
      let init_el := esuccess nil in
      let proc_one (e:laergo_expr) (acc:eresult (list ergoc_expr)) : eresult (list ergoc_expr) :=
          elift2
            cons
            (ergo_expr_to_ergoc_expr ctxt e)
            acc
      in
      elift (ECallFun prov fname) (fold_right proc_one init_el el)
    | EMatch prov e0 ecases edefault =>
        let ec0 := ergo_expr_to_ergoc_expr ctxt e0 in
        let eccases :=
            let proc_one acc ecase :=
                eolift
                  (fun acc =>
                     elift (fun x => (fst ecase, x)::acc)
                           (ergo_expr_to_ergoc_expr ctxt (snd ecase))) acc
            in
            fold_left proc_one ecases (esuccess nil)
        in
        let ecdefault := ergo_expr_to_ergoc_expr ctxt edefault in
        eolift
          (fun ec0 : ergoc_expr =>
             eolift
               (fun eccases =>
                  elift
                    (fun ecdefault : ergoc_expr =>
                       EMatch prov ec0 eccases ecdefault)
                    ecdefault) eccases) ec0
    | EForeach prov foreachs econd e2 =>
      let init_e2 := elift (EUnaryOp prov OpBag) (ergo_expr_to_ergoc_expr ctxt e2) in
      let init_e :=
          match econd with
          | Some econd =>
            elift2
              (fun econd e2 =>
                 EIf prov
                     econd
                     e2
                     (EConst prov (dcoll nil)))
              (ergo_expr_to_ergoc_expr ctxt econd)
              init_e2
          | None => init_e2
          end
      in
      let proc_one (foreach:string * laergo_expr) (acc:eresult ergoc_expr) : eresult ergoc_expr :=
          let v := fst foreach in
          let e := ergo_expr_to_ergoc_expr ctxt (snd foreach) in
          elift (EUnaryOp prov OpFlatten)
                (eolift (fun single =>
                           elift
                             (EForeach prov
                                       ((v,single)::nil)
                                       None) acc) (* Single foreach without where *)
                        e)
      in
      fold_right proc_one init_e foreachs
    end.

  (** Translate an Ergo statement to an Ergo expression *)
  Fixpoint ergo_stmt_to_expr (ctxt:translation_context) (s:laergo_stmt) : eresult ergoc_expr :=
    match s with
    | SReturn prov e =>
      elift (fun e =>
               ESuccess prov
                        (mkResult
                           prov
                           e
                           (EVar prov local_state)
                           (EVar prov local_emit)))
            (ergo_expr_to_ergoc_expr ctxt e)
    | SFunReturn prov e => (* Returning from a function does not have state or emit, just the result *)
      ergo_expr_to_ergoc_expr ctxt e
    | SThrow prov e =>
      elift (EError prov)
            (ergo_expr_to_ergoc_expr ctxt e)
    | SCallClause prov fname el =>
      match ctxt.(trans_ctxt_current_contract) with
      | None => not_in_contract_error prov
      | Some _ =>
        let el := emaplift (ergo_expr_to_ergoc_expr ctxt) el in
        elift (fun el =>
                 ECallFun prov
                          fname
                          ((thisContract prov)
                             ::(EVar prov local_state)
                             ::(EVar prov local_emit)
                             ::el)) el
      end
    | SSetState prov e1 s2 =>
      elift2 (setState prov)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_stmt_to_expr ctxt s2)
    | SEmit prov e1 s2 =>
      elift2 (pushEmit prov)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_stmt_to_expr ctxt s2)
    | SLet prov vname vtype e1 s2 =>
      elift2
        (ELet prov vname vtype)
        (ergo_expr_to_ergoc_expr ctxt e1)
        (ergo_stmt_to_expr ctxt s2)
    | SIf prov e1 s2 s3 =>
      elift3
        (EIf prov)
             (ergo_expr_to_ergoc_expr ctxt e1)
             (ergo_stmt_to_expr ctxt s2)
             (ergo_stmt_to_expr ctxt s3)
    | SEnforce prov e1 None s3 =>
      elift3 (EIf prov)
             (elift (EUnaryOp prov OpNeg) (ergo_expr_to_ergoc_expr ctxt e1))
             (esuccess (EError prov (EConst prov enforce_error_content)))
             (ergo_stmt_to_expr ctxt s3)
    | SEnforce prov e1 (Some s2) s3 =>
      elift3 (EIf prov)
             (elift (EUnaryOp prov OpNeg) (ergo_expr_to_ergoc_expr ctxt e1))
             (ergo_stmt_to_expr ctxt s2)
             (ergo_stmt_to_expr ctxt s3)
    | SMatch prov e0 scases sdefault =>
      let ec0 := ergo_expr_to_ergoc_expr ctxt e0 in
      let sccases :=
          let proc_one acc scase :=
              eolift
                (fun acc =>
                   elift (fun x => (fst scase, x)::acc)
                         (ergo_stmt_to_expr ctxt (snd scase))) acc
          in
          fold_left proc_one scases (esuccess nil)
      in
      let scdefault := ergo_stmt_to_expr ctxt sdefault in
      eolift
        (fun ec0 : ergoc_expr =>
           eolift
             (fun sccases =>
                elift
                  (fun scdefault : ergoc_expr =>
                     EMatch prov ec0 sccases scdefault)
                  scdefault) sccases) ec0
    end.

  Definition ergo_stmt_to_expr_top (ctxt:translation_context) (prov:provenance) (e:ergo_stmt) : eresult ergoc_expr :=
    elift (fun e =>
             ELet prov
                  local_state
                  None
                  (EVar prov this_state)
                  (ELet prov local_emit None
                        (EVar prov this_emit)
                        e))
          (ergo_stmt_to_expr ctxt e).

  (** Translate a clause to clause+calculus *)

  Definition clause_to_calculus
             (ctxt:translation_context)
             (tem:laergo_type)
             (sta:option laergo_type)
             (c:laergo_clause) : eresult ergoc_function :=
    let ctxt : translation_context := set_current_clause ctxt c.(clause_name) in
    (* XXX keep track of clause provenance *)
    let prov := ProvClause (loc_of_provenance c.(clause_annot)) c.(clause_name) in
    let response_type := c.(clause_sig).(type_signature_output) in
    let emit_type := lift_default_emits_type prov c.(clause_sig).(type_signature_emits) in
    let state_type :=  lift_default_state_type prov sta in
    let success_type := mk_success_type prov response_type state_type emit_type in
    let throw_type := lift_default_throws_type prov c.(clause_sig).(type_signature_throws) in
    let error_type := mk_error_type prov throw_type in
    let body :=
        match c.(clause_body) with
        | None => esuccess None
        | Some stmt =>
          elift Some (ergo_stmt_to_expr_top ctxt prov stmt)
        end
    in
    elift
      (mkFuncC
         prov
         c.(clause_name)
             (mkSigC
                ((this_contract, tem)
                   ::(this_state, state_type)
                   ::(this_emit, ErgoTypeArray prov emit_type)
                   ::c.(clause_sig).(type_signature_params))
                (mk_output_type prov success_type error_type)))
      body.

  (** Translate a function to function+calculus *)
  Definition function_to_calculus
             (ctxt:translation_context)
             (f:laergo_function) : eresult ergoc_function :=
    let prov := f.(function_annot) in
    let body :=
        match f.(function_body) with
        | None => esuccess None
        | Some stmt =>
          elift Some (ergo_stmt_to_expr_top ctxt prov stmt)
        end
    in
    elift
      (mkFuncC
        f.(function_annot)
        f.(function_name)
        (mkSigC
          f.(function_sig).(type_signature_params)
          f.(function_sig).(type_signature_output)))
      body.

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the comp_context *)

  Definition contract_to_calculus
             (ctxt:translation_context)
             (c:laergo_contract) : eresult ergoc_contract :=
    let ctxt :=
        set_current_contract ctxt c.(contract_name)
    in
    let clauses :=
        emaplift (clause_to_calculus ctxt c.(contract_template) c.(contract_state)) c.(contract_clauses)
    in
    elift
      (mkContractC
         c.(contract_annot)
         c.(contract_name))
      clauses.

  (** Translate a statement to a statement+calculus *)
  Definition declaration_to_calculus
             (d:laergo_declaration) : eresult (option (ergoc_declaration)) :=
    let ctxt := initial_translation_context in (* XXX For now only needs context per declaration *)
    match d with
    | DType prov ergo_type => esuccess None
    | DStmt prov s => elift Some (elift (DCExpr prov) (ergo_stmt_to_expr_top ctxt prov s))
    | DConstant prov v e => elift Some (elift (DCConstant prov v) (ergo_expr_to_ergoc_expr ctxt e))
    | DFunc prov f => elift Some (elift (DCFunc prov) (function_to_calculus ctxt f))
    | DContract prov c => elift Some (elift (DCContract prov) (contract_to_calculus ctxt c))
    end.

  (** Translate a module to a module+calculus *)
  Definition declarations_calculus
             (dl:list ergo_declaration) : eresult (list ergoc_declaration) :=
    let proc_one
          (d:ergo_declaration)
          (acc:eresult (list ergoc_declaration))
        : eresult (list ergoc_declaration) :=
        eolift (fun d =>
                 match d with
                 | None => acc
                 | Some edecl => elift (fun acc => cons edecl acc) acc
                 end)
              (declaration_to_calculus d)
    in
    fold_right proc_one (esuccess nil) dl.

  (** Translate a module to a module+calculus *)
  Definition ergo_module_to_calculus
             (p:laergo_module) : eresult ergoc_module :=
    elift
      (mkModuleC
         p.(module_annot)
         p.(module_namespace))
      (declarations_calculus p.(module_declarations)).

  Definition ergo_modules_to_calculus (pl:list laergo_module) : eresult (list ergoc_module) :=
    emaplift ergo_module_to_calculus pl.

  Section Examples.
    Definition f1 : laergo_function :=
      mkFunc dummy_provenance
             "addFee"%string
             (mkErgoTypeSignature
                dummy_provenance
                (("rate"%string, ErgoTypeDouble dummy_provenance)::nil)
                (ErgoTypeAny dummy_provenance)
                None
                None)
             (Some (SReturn dummy_provenance (EConst dummy_provenance (dfloat float_one)))).
    Definition f2 : laergo_function :=
      mkFunc dummy_provenance
             "addFee"%string
             (mkErgoTypeSignature
                dummy_provenance
                (("rate"%string, ErgoTypeDouble dummy_provenance)::nil)
                (ErgoTypeAny dummy_provenance)
                None
                None)
             (Some (SReturn dummy_provenance (EThisContract dummy_provenance))).
    Definition cl1 : laergo_clause :=
      mkClause dummy_provenance
               "volumediscount"%string
               (mkErgoTypeSignature
                  dummy_provenance
                  (("request"%string, ErgoTypeClassRef dummy_provenance default_request_absolute_name)::nil)
                  (ErgoTypeAny dummy_provenance)
                  None
                  None)
               (Some (SReturn
                        dummy_provenance
                        (ECallFun dummy_provenance "addFee"
                                  (EConst dummy_provenance (dfloat float_zero)::nil)))).
    Definition cl2 : laergo_clause :=
      mkClause dummy_provenance
               "volumediscount"%string
               (mkErgoTypeSignature
                  dummy_provenance
                  (("request"%string, ErgoTypeClassRef dummy_provenance default_request_absolute_name)::nil)
                  (ErgoTypeAny dummy_provenance)
                  None
                  None)
               (Some (SReturn
                        dummy_provenance
                        (ECallFun dummy_provenance "addFee"
                                  (EThisContract dummy_provenance::nil)))).
    Definition co1 : laergo_contract :=
      mkContract
        dummy_provenance
        "VolumeDiscount"%string
        (ErgoTypeClassRef dummy_provenance "TemplateModel"%string)
        None
        (cl1::cl2::nil).

    Definition dl1 : list laergo_declaration :=
      (DFunc dummy_provenance f1)
        :: (DContract dummy_provenance co1)
        :: nil.

    Definition dl2 : list laergo_declaration :=
      (DFunc dummy_provenance f1)
        :: (DFunc dummy_provenance f2)
        :: (DContract dummy_provenance co1)
        :: nil.

    (* Compute (declarations_calculus initial_translation_context dl1). (* Should succeed *) *)
    (* Compute (declarations_calculus initial_translation_context dl2). (* Should fail *) *)
  End Examples.

End ErgotoErgoCalculus.

