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

Require Import Qcert.NNRC.NNRCRuntime.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRCSugar.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRCCall.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCtoErgoNNRC.
  Section TranslationContext.
    Record translation_context :=
      mkTranslationContext {
          translation_context_fun_table: lookup_table;
          translation_context_params: list string;
        }.

    Definition add_params (ctxt:translation_context) (params:list string) : translation_context :=
      mkTranslationContext
        ctxt.(translation_context_fun_table)
        (List.app params ctxt.(translation_context_params)).

    Definition add_one_function (ctxt:translation_context) (fname:string) (flambda:lambdan) : translation_context :=
      mkTranslationContext
        (add_function_to_table ctxt.(translation_context_fun_table) fname flambda)
        ctxt.(translation_context_params).

  End TranslationContext.

  Definition ergo_pattern_to_nnrc (input_expr:nnrc_expr) (p:laergo_pattern) : (list string * nnrc_expr) :=
    match p with
    | CaseData prov d =>
      (nil, NNRCIf (NNRCBinop OpEqual input_expr (NNRCConst d))
                   (NNRCUnop OpLeft (NNRCConst (drec nil)))
                   (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseWildcard prov None =>
      (nil, NNRCUnop OpLeft (NNRCConst (drec nil)))
    | CaseWildcard prov (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (nil, NNRCEither
              (NNRCUnop (OpCast (type_name::nil)) input_expr)
              v1 (NNRCUnop OpLeft (NNRCConst (drec nil)))
              v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLet prov v None =>
      (v::nil, NNRCUnop OpLeft (NNRCUnop (OpRec v) input_expr))
    | CaseLet prov v (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 (NNRCUnop (OpCast (type_name::nil)) input_expr)
                 v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLetOption prov v None =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 input_expr
                 v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLetOption prov v (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 input_expr
                 v1 (NNRCEither
                       (NNRCUnop (OpCast (type_name::nil)) (NNRCVar v1))
                       v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                       v2 (NNRCUnop OpRight (NNRCConst dunit)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    end.

  Definition pack_pattern
             (vars:list string)
             (pattern_expr:nnrc_expr)
             (else_expr:nnrc_expr)
             (cont_expr:nnrc_expr)
    : nnrc_expr :=
    let v_rec := fresh_in_case pattern_expr else_expr in
    let init_expr := else_expr in
    let proc_one (acc:nnrc_expr) (v:string) :=
        NNRCLet v (NNRCUnop (OpDot v) (NNRCVar v_rec)) acc
    in
    let inner_expr :=
        fold_left proc_one vars init_expr
    in
    let (v1,v2) := fresh_var2 "$case" "$case" nil in
    NNRCEither
      pattern_expr
      v1 (NNRCLet v_rec
                  (NNRCVar v1)
                  inner_expr)
      v2 cont_expr
  .

  (** Translate calculus expressions to NNRC *)
  Fixpoint ergoc_expr_to_nnrc
           (ctxt:translation_context) (e:ergoc_expr) : eresult nnrc_expr :=
    match e with
    | EThisContract prov => contract_in_calculus_error prov (* XXX We should prove it never happens *)
    | EThisClause prov => clause_in_calculus_error prov (* XXX We should prove it never happens *)
    | EThisState prov => state_in_calculus_error prov (* XXX We should prove it never happens *)
    | EVar prov v =>
      if in_dec string_dec v ctxt.(translation_context_params)
      then esuccess (NNRCGetConstant v)
      else esuccess (NNRCVar v)
    | EConst prov d =>
      esuccess (NNRCConst d)
    | EArray prov el =>
      let init_el := esuccess nil in
      let proc_one (e:ergo_expr) (acc:eresult (list nnrc_expr)) : eresult (list nnrc_expr) :=
          elift2
            cons
            (ergoc_expr_to_nnrc ctxt e)
            acc
      in
      elift new_array (fold_right proc_one init_el el)
    | EUnaryOp prov u e =>
      elift (NNRCUnop u)
            (ergoc_expr_to_nnrc ctxt e)
    | EBinaryOp prov b e1 e2 =>
      elift2 (NNRCBinop b)
             (ergoc_expr_to_nnrc ctxt e1)
             (ergoc_expr_to_nnrc ctxt e2)
    | EIf prov e1 e2 e3 =>
      elift3 NNRCIf
        (ergoc_expr_to_nnrc ctxt e1)
        (ergoc_expr_to_nnrc ctxt e2)
        (ergoc_expr_to_nnrc ctxt e3)
    | ELet prov v None e1 e2 =>
      elift2 (NNRCLet v)
              (ergoc_expr_to_nnrc ctxt e1)
              (ergoc_expr_to_nnrc ctxt e2)
    | ELet prov v (Some t1) e1 e2 => (** XXX TYPE IS IGNORED AT THE MOMENT *)
      elift2 (NNRCLet v)
              (ergoc_expr_to_nnrc ctxt e1)
              (ergoc_expr_to_nnrc ctxt e2)
    | ENew prov cr nil =>
      esuccess (new_expr cr (NNRCConst (drec nil)))
    | ENew prov cr ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoc_expr_to_nnrc ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoc_expr_to_nnrc ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 acc (elift (NNRCUnop (OpRec attname)) e)
      in
      elift (new_expr cr) (fold_left proc_one rest init_rec)
    | ERecord prov nil =>
      esuccess (NNRCConst (drec nil))
    | ERecord prov ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoc_expr_to_nnrc ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoc_expr_to_nnrc ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 acc (elift (NNRCUnop (OpRec attname)) e)
      in
      fold_left proc_one rest init_rec
    | ECallFun prov fname el =>
      let init_el := esuccess nil in
      let proc_one (e:ergo_expr) (acc:eresult (list nnrc_expr)) : eresult (list nnrc_expr) :=
          elift2
            cons
            (ergoc_expr_to_nnrc ctxt e)
            acc
      in
      eolift (lookup_call prov ctxt.(translation_context_fun_table) fname) (fold_right proc_one init_el el)
    | EMatch prov e0 ecases edefault =>
      let ec0 := ergoc_expr_to_nnrc ctxt e0 in
      let eccases :=
          let proc_one acc ecase :=
              eolift
                (fun acc =>
                   elift (fun x => (fst ecase, x)::acc)
                         (ergoc_expr_to_nnrc ctxt (snd ecase))) acc
          in
          fold_left proc_one ecases (esuccess nil)
      in
      let ecdefault := ergoc_expr_to_nnrc ctxt edefault in
      eolift
        (fun ec0 : nnrc_expr =>
           eolift
             (fun eccases =>
                eolift
                  (fun ecdefault =>
                     let v0 : string := fresh_in_match eccases ecdefault in
                     let proc_one_case
                           (acc:eresult nnrc_expr)
                           (ecase:ergo_pattern * nnrc_expr)
                         : eresult nnrc_expr :=
                         let (vars, pattern_expr) := ergo_pattern_to_nnrc (NNRCVar v0) (fst ecase) in
                         elift
                           (fun cont_expr : nnrc_expr =>
                              pack_pattern
                                vars
                                pattern_expr
                                (snd ecase)
                                cont_expr)
                           acc
                     in
                     let eccases_folded : eresult nnrc_expr :=
                         fold_left proc_one_case eccases (esuccess ecdefault)
                     in
                     elift (NNRCLet v0 ec0) eccases_folded)
                  ecdefault) eccases) ec0
    | EForeach loc ((v,e1)::nil) None e2 =>
      elift2
        (NNRCFor v)
        (ergoc_expr_to_nnrc ctxt e1)
        (ergoc_expr_to_nnrc ctxt e2)
    | EForeach prov _ _ _ =>
      complex_foreach_in_calculus_error prov (* XXX We should prove it never happens *)
    end.

  (** Translate a function to function+calculus *)
  Definition functionc_to_nnrc
             (ctxt:translation_context)
             (fn:absolute_name)
             (f:ergoc_function) : eresult nnrc_function :=
    let ctxt : translation_context :=
        add_params ctxt (List.map fst f.(functionc_sig).(sigc_params))
    in
    match f.(functionc_body) with
    | Some body =>
      elift
        (mkFuncN fn)
        (elift
           (mkLambdaN
              f.(functionc_sig).(sigc_params)
              f.(functionc_sig).(sigc_output))
           (ergoc_expr_to_nnrc ctxt body))
    | None =>
      let rlambda := lookup_lambda f.(functionc_annot) nnrc_stdlib fn in
      elift
        (mkFuncN fn)
        rlambda
    end.

  (** Translate a declaration to a declaration+calculus *)
  Definition clausec_declaration_to_nnrc
             (ctxt:translation_context)
             (fn:absolute_name)
             (f:ergoc_function) : eresult (translation_context * nnrc_function) :=
    elift
      (fun x => (add_one_function
                   ctxt
                   x.(functionn_name)
                   x.(functionn_lambda), x)) (* Add new function to translation_context *)
      (functionc_to_nnrc ctxt fn f).

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the translation_context *)
  Definition contractc_to_nnrc
             (ctxt:translation_context)
             (cn:local_name)
             (c:ergoc_contract) : eresult (translation_context * nnrc_function_table) :=
    let init := esuccess (ctxt, nil) in
    let proc_one
          (acc:eresult (translation_context * list nnrc_function))
          (s:absolute_name * ergoc_function)
        : eresult (translation_context * list nnrc_function) :=
        eolift
          (fun acc : translation_context * list nnrc_function =>
             let (ctxt,acc) := acc in
             elift (fun xy : translation_context * nnrc_function =>
                      let (newctxt,news) := xy in
                      (newctxt,news::acc))
                   (clausec_declaration_to_nnrc ctxt (fst s) (snd s)))
          acc
    in
    elift
      (fun xy =>
         (fst xy,
          (mkFuncTableN
             cn
             (snd xy))))
      (List.fold_left proc_one c.(contractc_clauses) init).

  (** Translate a statement to a statement+calculus *)
  Definition declaration_to_nnrc
             (ctxt:translation_context) (s:ergoc_declaration) : eresult (translation_context * nnrc_declaration) :=
    match s with
    | DCExpr prov e =>
      elift
        (fun x => (ctxt, DNExpr x))
        (ergoc_expr_to_nnrc ctxt e)
    | DCConstant prov v e =>
      elift
        (fun x => (ctxt, DNConstant v x)) (* Add new variable to translation_context *)
        (ergoc_expr_to_nnrc ctxt e)
    | DCFunc prov fn f =>
      elift
        (fun x => (add_one_function ctxt x.(functionn_name) x.(functionn_lambda), DNFunc x)) (* Add new function to translation_context *)
        (functionc_to_nnrc ctxt fn f)
    | DCContract prov cn c =>
      elift (fun xy => (fst xy, DNFuncTable (snd xy)))
            (contractc_to_nnrc ctxt cn c)
    end.

  Definition init_translation_context :=
    mkTranslationContext nnrc_stdlib nil.

  (** Translate a module to a module+calculus *)
  Definition declarations_calculus_with_table (dl:list ergoc_declaration)
    : eresult (translation_context * list nnrc_declaration) :=
    let ctxt := init_translation_context in
    let init := esuccess (ctxt, nil) in
    let proc_one
          (acc:eresult (translation_context * list nnrc_declaration))
          (s:ergoc_declaration)
        : eresult (translation_context * list nnrc_declaration) :=
        eolift
          (fun acc : translation_context * list nnrc_declaration =>
             let (ctxt,acc) := acc in
             let edecl := declaration_to_nnrc ctxt s in
               elift (fun xy : translation_context * nnrc_declaration =>
                        let (newctxt,news) := xy in
                        (newctxt,news::acc))
               edecl)
          acc
    in
    List.fold_left proc_one dl init.

  (** Translate a module to a module+calculus *)
  Definition module_to_nnrc_with_table (p:ergoc_module) : eresult nnrc_module :=
    elift
      (fun xy =>
         (mkModuleN
            p.(modulec_namespace)
                (snd xy)))
      (declarations_calculus_with_table p.(modulec_declarations)).

  Definition ergoc_module_to_nnrc (m:ergoc_module) : eresult nnrc_module :=
    module_to_nnrc_with_table m.

  Section Examples.
    Open Scope string.
    Definition ctxt0 := init_translation_context.

    (**r Test pattern matching on values *)
    Definition input1 := dnat 2.
    
    Example j1 : ergoc_expr :=
      EMatch dummy_provenance
             (EConst dummy_provenance input1)
             ((CaseData dummy_provenance (dnat 1), EConst dummy_provenance (dstring "1"))
                :: (CaseData dummy_provenance (dnat 2), EConst dummy_provenance (dstring "2"))
                :: nil)
             (EConst dummy_provenance (dstring "lots")).
    Definition jc1 := ergoc_expr_to_nnrc ctxt0 j1.
    (* Compute jc1. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc1. *)

    Example j1' : laergo_expr :=
      EMatch dummy_provenance
             (EConst dummy_provenance input1)
             ((CaseData dummy_provenance (dnat 1), EConst dummy_provenance (dstring "1"))
                :: (CaseLet dummy_provenance "v2" None, EVar dummy_provenance "v2")
                :: nil)
             (EConst dummy_provenance (dstring "lots")).
    Definition jc1' := ergoc_expr_to_nnrc ctxt0 j1'.
    (* Compute jc1'. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc1'. *)

    (**r Test pattern matching on type names *)
    Definition input2 :=
      dbrand ("C2"::nil) (dnat 1).
    
    Example j2 : laergo_expr :=
      EMatch dummy_provenance
             (EConst dummy_provenance input2)
             ((CaseLet dummy_provenance "v1" (Some "C1"), EConst dummy_provenance (dstring "1"))
                :: (CaseLet dummy_provenance "v2" (Some "C2"), EConst dummy_provenance (dstring "2"))
                :: nil)
             (EConst dummy_provenance (dstring "lots")).

    Definition jc2 := ergoc_expr_to_nnrc ctxt0 j2.
    (* Compute jc2. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc2. *)

    (**r Test pattern matching on optional *)
    Definition input3 :=
      dsome (dnat 1).
    
    Definition input3none :=
      dnone.
    
    Example j3 input : laergo_expr :=
      EMatch dummy_provenance
             (EConst dummy_provenance input)
             ((CaseLetOption dummy_provenance "v1" None, EConst dummy_provenance (dstring "1"))
                :: nil)
             (EConst dummy_provenance (dstring "nothing")).

    Definition jc3 := ergoc_expr_to_nnrc ctxt0 (j3 input3).
    Definition jc3none := ergoc_expr_to_nnrc ctxt0 (j3 input3none).
    (* Compute jc3. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc3. *)
    (* Compute jc3none. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc3none. *)

    Example j4 : laergo_expr :=
      EForeach dummy_provenance
               (("x", EConst dummy_provenance (dcoll (dnat 1::dnat 2::dnat 3::nil)))
                  :: ("y", EConst dummy_provenance (dcoll (dnat 4::dnat 5::dnat 6::nil)))
                  :: nil)
               None
               (ERecord dummy_provenance
                        (("a",EVar dummy_provenance "x")
                           ::("b",EVar dummy_provenance "y")
                           ::nil)).
    Definition jc4 := ergoc_expr_to_nnrc ctxt0 j4.
    (* Compute jc4. *)

    Example j5 : laergo_expr :=
      EForeach dummy_provenance
               (("x", EConst dummy_provenance (dcoll (dnat 1::dnat 2::dnat 3::nil)))
                  :: ("y", EConst dummy_provenance (dcoll (dnat 4::dnat 5::dnat 6::nil)))
                  :: nil)
               None
               (ENew dummy_provenance
                     "person"
                     (("a",EVar dummy_provenance "x")
                        ::("b",EVar dummy_provenance "y")
                        ::nil)).
    Definition jc5 := ergoc_expr_to_nnrc ctxt0 j5.
    (* Compute jc5. *)

  End Examples.

End ErgoCtoErgoNNRC.

