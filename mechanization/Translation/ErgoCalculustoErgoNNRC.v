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
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRCSugar.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRCCall.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculustoErgoNNRC.

  Section TranslationContext.
    Record comp_context :=
      mkCompContext {
          comp_context_ctos : list cto_declaration;
          comp_context_current_contract : option string;
          comp_context_current_clause : option string;
          comp_context_fun_table: lookup_table;
          comp_context_namespace: string;
          comp_context_globals: list string;
          comp_context_params: list string;
        }.

    Definition add_globals (ctxt:comp_context) (params:list string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        ctxt.(comp_context_current_clause)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        (List.app params ctxt.(comp_context_globals))
        ctxt.(comp_context_params).

    Definition add_params (ctxt:comp_context) (params:list string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        ctxt.(comp_context_current_clause)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        ctxt.(comp_context_globals)
        (List.app params ctxt.(comp_context_params)).

    Definition add_one_global (ctxt:comp_context) (param:string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        ctxt.(comp_context_current_clause)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        (List.cons param ctxt.(comp_context_globals))
        ctxt.(comp_context_params).

    Definition add_one_param (ctxt:comp_context) (param:string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        ctxt.(comp_context_current_clause)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        ctxt.(comp_context_globals)
        (List.cons param ctxt.(comp_context_params)).

    Definition add_one_function (ctxt:comp_context) (fname:string) (flambda:lambdan) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        ctxt.(comp_context_current_clause)
        (add_function_to_table ctxt.(comp_context_fun_table) fname flambda)
        ctxt.(comp_context_namespace)
        ctxt.(comp_context_globals)
        ctxt.(comp_context_params).

    Definition set_current_contract (ctxt:comp_context) (cname:string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        (Some cname)
        ctxt.(comp_context_current_clause)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        ctxt.(comp_context_globals)
        ctxt.(comp_context_params).
  
    Definition set_current_clause (ctxt:comp_context) (cname:string) : comp_context :=
      mkCompContext
        ctxt.(comp_context_ctos)
        ctxt.(comp_context_current_contract)
        (Some cname)
        ctxt.(comp_context_fun_table)
        ctxt.(comp_context_namespace)
        ctxt.(comp_context_globals)
        ctxt.(comp_context_params).

  End TranslationContext.

  Definition ergo_pattern_to_nnrc (input_expr:nnrc_expr) (p:ergo_pattern) : (list string * nnrc_expr) :=
    match p with
    | CaseData d =>
      (nil, NNRCIf (NNRCBinop OpEqual input_expr (NNRCConst d))
                   (NNRCUnop OpLeft (NNRCConst (drec nil)))
                   (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseWildcard None =>
      (nil, NNRCUnop OpLeft (NNRCConst (drec nil)))
    | CaseWildcard (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (nil, NNRCEither
              (NNRCUnop (OpCast (type_name::nil)) input_expr)
              v1 (NNRCUnop OpLeft (NNRCConst (drec nil)))
              v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLet v None =>
      (v::nil, NNRCUnop OpLeft (NNRCUnop (OpRec v) input_expr))
    | CaseLet v (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 (NNRCUnop (OpCast (type_name::nil)) input_expr)
                 v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLetOption v None =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 input_expr
                 v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLetOption v (Some type_name) =>
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

  (** Translate expressions to calculus *)
  Fixpoint ergoc_expr_to_nnrc
           (ctxt:comp_context) (e:ergoc_expr) : eresult nnrc_expr :=
    match e with
    | EThisContract =>
      match ctxt.(comp_context_current_contract) with
      | None => not_in_contract_error
      | Some _ => esuccess (NNRCVar local_contract)
      end
    | EThisClause => 
      match ctxt.(comp_context_current_clause) with
      | None => not_in_clause_error
      | Some cname => esuccess (NNRCUnop (OpDot cname) (NNRCUnop OpUnbrand (NNRCVar local_contract)))
      end
    | EThisState =>
      match ctxt.(comp_context_current_contract) with
      | None => not_in_contract_error
      | Some _ => esuccess (NNRCVar local_state)
      end
    | EVar v =>
      if in_dec string_dec v ctxt.(comp_context_params)
      then esuccess (NNRCGetConstant v)
      else esuccess (NNRCVar v)
    | EConst d =>
      esuccess (NNRCConst d)
    | EArray el =>
      let init_el := esuccess nil in
      let proc_one (acc:eresult (list nnrc_expr)) (e:ergo_expr) : eresult (list nnrc_expr) :=
          elift2
            cons
            (ergoc_expr_to_nnrc ctxt e)
            acc
      in
      elift new_array (fold_left proc_one el init_el)
    | EUnaryOp u e =>
      elift (NNRCUnop u)
            (ergoc_expr_to_nnrc ctxt e)
    | EBinaryOp b e1 e2 =>
      elift2 (NNRCBinop b)
             (ergoc_expr_to_nnrc ctxt e1)
             (ergoc_expr_to_nnrc ctxt e2)
    | EIf e1 e2 e3 =>
      elift3 NNRCIf
        (ergoc_expr_to_nnrc ctxt e1)
        (ergoc_expr_to_nnrc ctxt e2)
        (ergoc_expr_to_nnrc ctxt e3)
    | ELet v None e1 e2 =>
      elift2 (NNRCLet v)
              (ergoc_expr_to_nnrc ctxt e1)
              (ergoc_expr_to_nnrc ctxt e2)
    | ELet v (Some t1) e1 e2 => (** XXX TYPE IS IGNORED AT THE MOMENT *)
      elift2 (NNRCLet v)
              (ergoc_expr_to_nnrc ctxt e1)
              (ergoc_expr_to_nnrc ctxt e2)
    | ENew cr nil =>
      esuccess
        (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr) (NNRCConst (drec nil)))
    | ENew cr ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoc_expr_to_nnrc ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoc_expr_to_nnrc ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 (elift (NNRCUnop (OpRec attname)) e) acc
      in
      elift (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr)) (fold_left proc_one rest init_rec)
    | ERecord nil =>
      esuccess
        (NNRCConst (drec nil))
    | ERecord ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoc_expr_to_nnrc ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoc_expr_to_nnrc ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 (elift (NNRCUnop (OpRec attname)) e) acc
      in
      fold_left proc_one rest init_rec
    | ECallFun fname el =>
      let init_el := esuccess nil in
      let proc_one (e:ergo_expr) (acc:eresult (list nnrc_expr)) : eresult (list nnrc_expr) :=
          elift2
            cons
            (ergoc_expr_to_nnrc ctxt e)
            acc
      in
      eolift (lookup_call ctxt.(comp_context_fun_table) fname) (fold_right proc_one init_el el)
    | EMatch e0 ecases edefault =>
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
    | EForeach foreachs None e2 =>
      let init_e := ergoc_expr_to_nnrc ctxt e2 in
      let proc_one (acc:eresult nnrc) (foreach:string * ergo_expr) : eresult nnrc :=
          let v := fst foreach in
          let e := ergoc_expr_to_nnrc ctxt (snd foreach) in
          elift2 (NNRCFor v)
                 e
                 acc
      in
      fold_left proc_one foreachs init_e
    | EForeach foreachs (Some econd) e2 =>
      let init_e :=
          elift2
            (fun econd e2 =>
               NNRCIf econd
                     (NNRCUnop OpBag e2)
                     (NNRCConst (dcoll nil)))
            (ergoc_expr_to_nnrc ctxt econd)
            (ergoc_expr_to_nnrc ctxt e2)
      in
      let proc_one (acc:eresult nnrc) (foreach:string * ergo_expr) : eresult nnrc :=
          let v := fst foreach in
          let e := ergoc_expr_to_nnrc ctxt (snd foreach) in
          elift2 (NNRCFor v)
                 e
                 acc
      in
      elift (NNRCUnop OpFlatten)
            (fold_left proc_one foreachs init_e)
    | ELiftError e e1 =>
      elift2
        (fun ec ec1 =>
           let (v1,v2) := fresh_in_lift_error ec1 in
           NNRCEither
             ec
             v1 ec1
             v2 (NNRCVar v2))
        (ergoc_expr_to_nnrc ctxt e)
        (ergoc_expr_to_nnrc ctxt e1)
    end.

  (** Translate a clause to clause+calculus *)

  Definition clausec_to_nnrc
             (ctxt:comp_context) (c:ergoc_clause) : eresult nnrc_clause :=
    let ctxt : comp_context :=
        set_current_clause ctxt c.(clausec_name)
    in
    let ctxt : comp_context :=
        add_params
          ctxt
          (List.map fst c.(clausec_lambda).(lambdac_params))
    in
    elift
      (mkClauseN
         c.(clausec_name))
      (elift
         (mkLambdaN
            c.(clausec_lambda).(lambdac_params)
            c.(clausec_lambda).(lambdac_output)
            c.(clausec_lambda).(lambdac_throws)
            c.(clausec_lambda).(lambdac_emits))
         (ergoc_expr_to_nnrc ctxt c.(clausec_lambda).(lambdac_body))).

  (** Translate a function to function+calculus *)
  Definition functionc_to_nnrc
             (ctxt:comp_context) (f:ergoc_function) : eresult nnrc_function :=
    let ctxt :=
        add_params ctxt (List.map fst f.(functionc_lambda).(lambdac_params))
    in
    elift
      (mkFuncN
         f.(functionc_name))
      (elift
         (mkLambdaN
            f.(functionc_lambda).(lambdac_params)
            f.(functionc_lambda).(lambdac_output)
            f.(functionc_lambda).(lambdac_throws)
            f.(functionc_lambda).(lambdac_emits))
         (ergoc_expr_to_nnrc ctxt f.(functionc_lambda).(lambdac_body))).

  (** Translate a declaration to a declaration+calculus *)
  Definition clausec_declaration_to_nnrc
             (ctxt:comp_context) (c:ergoc_clause) : eresult (comp_context * nnrc_clause) :=
    elift
      (fun x => (add_one_function
                   ctxt
                   x.(clausen_name)
                   x.(clausen_lambda), x)) (* Add new function to comp_context *)
      (clausec_to_nnrc ctxt c).

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the comp_context *)

  Definition contractc_to_nnrc
             (ctxt:comp_context) (c:ergoc_contract) : eresult (comp_context * nnrc_contract) :=
    let ctxt :=
        set_current_contract ctxt c.(contractc_name)
    in
    let ctxt : comp_context :=
        add_params
          ctxt
          (current_time :: this_contract :: this_state :: this_emit :: nil)
    in
    let init := esuccess (ctxt, nil) in
    let proc_one
          (acc:eresult (comp_context * list nnrc_clause))
          (s:ergoc_clause)
        : eresult (comp_context * list nnrc_clause) :=
        eolift
          (fun acc : comp_context * list nnrc_clause =>
             let (ctxt,acc) := acc in
             elift (fun xy : comp_context * nnrc_clause =>
                      let (newctxt,news) := xy in
                      (newctxt,news::acc))
                   (clausec_declaration_to_nnrc ctxt s))
          acc
    in
    let cl : list ergoc_clause := c.(contractc_clauses) in
    elift
      (fun xy =>
         (fst xy,
          (mkContractN
             c.(contractc_name)
             c.(contractc_template)
             (snd xy))))
      (List.fold_left proc_one cl init).

  (** Translate a statement to a statement+calculus *)
  Definition declaration_to_nnrc
             (ctxt:comp_context) (s:ergoc_declaration) : eresult (comp_context * nnrc_declaration) :=
    match s with
    | ECExpr e =>
      elift
        (fun x => (ctxt, ENExpr x))
        (ergoc_expr_to_nnrc ctxt e)
    | ECGlobal v e =>
      elift
        (fun x => (add_one_global ctxt v, ENGlobal v x)) (* Add new variable to comp_context *)
        (ergoc_expr_to_nnrc ctxt e)
    | ECFunc f =>
      elift
        (fun x => (add_one_function ctxt x.(functionn_name) x.(functionn_lambda), ENFunc x)) (* Add new function to comp_context *)
        (functionc_to_nnrc ctxt f)
    | ECContract c =>
      elift (fun xy => (fst xy, ENContract (snd xy)))
            (contractc_to_nnrc ctxt c)
    end.

  Definition initial_comp_context (ctos:list cto_declaration) (p:string) :=
    mkCompContext ctos None None nnrc_stdlib p nil nil.

  (** Translate a package to a package+calculus *)
  Definition declarations_calculus_with_table
             (cto_decls:list cto_declaration) (local_namespace:string) (dl:list ergoc_declaration)
    : eresult (comp_context * list nnrc_declaration) :=
    let ctxt := initial_comp_context cto_decls local_namespace in
    let init := esuccess (ctxt, nil) in
    let proc_one
          (acc:eresult (comp_context * list nnrc_declaration))
          (s:ergoc_declaration)
        : eresult (comp_context * list nnrc_declaration) :=
        eolift
          (fun acc : comp_context * list nnrc_declaration =>
             let (ctxt,acc) := acc in
             let edecl := declaration_to_nnrc ctxt s in
               elift (fun xy : comp_context * nnrc_declaration =>
                        let (newctxt,news) := xy in
                        (newctxt,news::acc))
               edecl)
          acc
    in
    List.fold_left proc_one dl init.

  (** Translate a package to a package+calculus *)
  Definition package_to_nnrc_with_table
             (cto_decls:list cto_declaration) (local_namespace:string) (p:ergoc_package) : eresult nnrc_package :=
    elift
      (fun xy =>
         (mkPackageN
            p.(packagec_namespace)
                (snd xy)))
      (declarations_calculus_with_table cto_decls local_namespace p.(packagec_declarations)).

  Definition package_to_nnrc (ctos:list cto_package) (p:ergoc_package) : eresult nnrc_package :=
    let local_namespace := p.(packagec_namespace) in
    let ectos := cto_resolved_tbl_for_package ctos in
    eolift (fun ctos_decls => package_to_nnrc_with_table ctos_decls local_namespace p) ectos.

  Section tests.
    Open Scope string.
    Definition ctxt0 := initial_comp_context nil "org.accordproject".

    (**r Test pattern matching on values *)
    Definition input1 := dnat 2.
    
    Example j1 :=
      EMatch (EConst input1)
              ((CaseData (dnat 1), (EConst (dstring "1")))
                 :: (CaseData (dnat 2), (EConst (dstring "2")))
                 :: nil)
              (EConst (dstring "lots")).
    Definition jc1 := ergoc_expr_to_nnrc ctxt0 j1.
    (* Eval vm_compute in jc1. *)
    (* Eval vm_compute in elift (fun x => nnrc_eval_top nil x nil) jc1. *)

    Example j1' :=
      EMatch (EConst input1)
              ((CaseData (dnat 1), (EConst (dstring "1")))
                 :: (CaseLet "v2" None, EVar "v2")
                 :: nil)
              (EConst (dstring "lots")).
    Definition jc1' := ergoc_expr_to_nnrc ctxt0 j1'.
    (* Eval vm_compute in jc1'. *)
    (* Eval vm_compute in elift (fun x => nnrc_eval_top nil x nil) jc1'. *)

    (**r Test pattern matching on type names *)
    Definition input2 :=
      dbrand ("C2"::nil) (dnat 1).
    
    Example j2 :=
      EMatch (EConst input2)
             ((CaseLet "v1" (Some "C1"), (EConst (dstring "1")))
                :: (CaseLet "v2" (Some "C2"), (EConst (dstring "2")))
                :: nil)
              (EConst (dstring "lots")).

    Definition jc2 := ergoc_expr_to_nnrc ctxt0 j2.
    (* Eval vm_compute in jc2. *)
    (* Eval vm_compute in elift (fun x => nnrc_eval_top nil x nil) jc2. *)

    (**r Test pattern matching on optional *)
    Definition input3 :=
      dsome (dnat 1).
    
    Definition input3none :=
      dnone.
    
    Example j3 input :=
      EMatch (EConst input)
             ((CaseLetOption "v1" None, (EConst (dstring "1")))
                :: nil)
              (EConst (dstring "nothing")).

    Definition jc3 := ergoc_expr_to_nnrc ctxt0 (j3 input3).
    Definition jc3none := ergoc_expr_to_nnrc ctxt0 (j3 input3none).
    (* Eval vm_compute in jc3. *)
    (* Eval vm_compute in elift (fun x => nnrc_eval_top nil x nil) jc3. *)
    (* Eval vm_compute in jc3none. *)
    (* Eval vm_compute in elift (fun x => nnrc_eval_top nil x nil) jc3none. *)

  End tests.
  
End ErgoCalculustoErgoNNRC.

