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
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRCSugar.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCTtoErgoNNRC.
  Context {m : brand_model}.

  Definition ergo_pattern_to_nnrc (input_expr:nnrc_expr) (p:tlaergo_pattern) : (list string * nnrc_expr) :=
    match p with
    | CaseData _ d =>
      (nil, NNRCIf (NNRCBinop OpEqual input_expr (NNRCConst d))
                   (NNRCUnop OpLeft (NNRCConst (drec nil)))
                   (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseWildcard _ None =>
      (nil, NNRCUnop OpLeft (NNRCConst (drec nil)))
    | CaseWildcard _ (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (nil, NNRCEither
              (NNRCUnop (OpCast (type_name::nil)) input_expr)
              v1 (NNRCUnop OpLeft (NNRCConst (drec nil)))
              v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLet _ v None =>
      (v::nil, NNRCUnop OpLeft (NNRCUnop (OpRec v) input_expr))
    | CaseLet _ v (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, NNRCEither
                 (NNRCUnop (OpCast (type_name::nil)) input_expr)
                 v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                 v2 (NNRCUnop OpRight (NNRCConst dunit)))
    | CaseLetOption _ v None =>
      let v1 := fresh_var "$case" nil in
      (v::nil, (NNRCLet v1 input_expr
                        (NNRCIf
                           (NNRCBinop OpEqual (NNRCVar v1) (NNRCConst dunit))
                           (NNRCUnop OpRight (NNRCConst dunit))
                           (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1))))))
    | CaseLetOption _ v (Some type_name) =>
      let (v1,v2) := fresh_var2 "$case" "$case" nil in
      (v::nil, (NNRCLet v1 input_expr
                        (NNRCIf
                           (NNRCBinop OpEqual (NNRCVar v1) (NNRCConst dunit))
                           (NNRCUnop OpRight (NNRCConst dunit))
                           (NNRCEither
                              (NNRCUnop (OpCast (type_name::nil)) (NNRCVar v1))
                              v1 (NNRCUnop OpLeft (NNRCUnop (OpRec v) (NNRCVar v1)))
                              v2 (NNRCUnop OpRight (NNRCConst dunit))))))
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
  Fixpoint ergoct_expr_to_nnrc
           (env:list string) (e:ergoct_expr) : eresult nnrc_expr :=
    match e with
    | EThisContract (prov,_) => contract_in_calculus_error prov (* XXX We should prove it never happens *)
    | EThisClause (prov,_) => clause_in_calculus_error prov (* XXX We should prove it never happens *)
    | EThisState (prov,_) => state_in_calculus_error prov (* XXX We should prove it never happens *)
    | EVar (prov,_) v =>
      if in_dec string_dec v env
      then esuccess (NNRCGetConstant v) nil
      else esuccess (NNRCVar v) nil
    | EConst (prov,_) d =>
      esuccess (NNRCConst d) nil
    | ENone (prov,_) => esuccess (NNRCConst dunit) nil (* XXX Not safe ! *)
    | ESome (prov,_) e => ergoct_expr_to_nnrc env e (* XXX Not safe ! *)
    | EArray (prov,_) el =>
      let init_el := esuccess nil nil in
      let proc_one (e:ergo_expr) (acc:eresult (list nnrc_expr)) : eresult (list nnrc_expr) :=
          elift2
            cons
            (ergoct_expr_to_nnrc env e)
            acc
      in
      elift new_array (fold_right proc_one init_el el)
    | EUnaryOperator (prov,_) u e =>
      operator_in_calculus_error prov (* XXX We should prove it never happens *)
    | EBinaryOperator (prov,_) b e1 e2 =>
      operator_in_calculus_error prov (* XXX We should prove it never happens *)
    | EUnaryBuiltin (prov,_) u e =>
      elift (NNRCUnop u)
            (ergoct_expr_to_nnrc env e)
    | EBinaryBuiltin (prov,_) b e1 e2 =>
      elift2 (NNRCBinop b)
             (ergoct_expr_to_nnrc env e1)
             (ergoct_expr_to_nnrc env e2)
    | EIf (prov,_) e1 e2 e3 =>
      elift3 NNRCIf
        (ergoct_expr_to_nnrc env e1)
        (ergoct_expr_to_nnrc env e2)
        (ergoct_expr_to_nnrc env e3)
    | ELet (prov,_) v None e1 e2 =>
      elift2 (NNRCLet v)
              (ergoct_expr_to_nnrc env e1)
              (ergoct_expr_to_nnrc env e2)
    | ELet (prov,_) v (Some t1) e1 e2 => (** XXX TYPE IS IGNORED AT THE MOMENT *)
      elift2 (NNRCLet v)
              (ergoct_expr_to_nnrc env e1)
              (ergoct_expr_to_nnrc env e2)
    | EPrint (prov,_) v e =>
      print_in_calculus_error prov
    | ENew (prov,_) cr nil =>
      esuccess (new_expr cr (NNRCConst (drec nil))) nil
    | ENew (prov,_) cr ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoct_expr_to_nnrc env init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoct_expr_to_nnrc env (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 acc (elift (NNRCUnop (OpRec attname)) e)
      in
      elift (new_expr cr) (fold_left proc_one rest init_rec)
    | ERecord (prov,_) nil =>
      esuccess (NNRCConst (drec nil)) nil
    | ERecord (prov,_) ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergoct_expr_to_nnrc env init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergoct_expr_to_nnrc env (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 acc (elift (NNRCUnop (OpRec attname)) e)
      in
      fold_left proc_one rest init_rec
    | ECallFun (prov,_) fname _ => function_not_inlined_error prov "ec2en/expr" fname
    | ECallFunInGroup (prov,_) gname fname _ => function_in_group_not_inlined_error prov gname fname
    | EMatch (prov,_) e0 ecases edefault =>
      let ec0 := ergoct_expr_to_nnrc env e0 in
      let eccases :=
          let proc_one acc ecase :=
              eolift
                (fun acc =>
                   elift (fun x => (fst ecase, x)::acc)
                         (ergoct_expr_to_nnrc env (snd ecase))) acc
          in
          fold_left proc_one ecases (esuccess nil nil)
      in
      let ecdefault := ergoct_expr_to_nnrc env edefault in
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
                         fold_left proc_one_case eccases (esuccess ecdefault nil)
                     in
                     elift (NNRCLet v0 ec0) eccases_folded)
                  ecdefault) eccases) ec0
    | EForeach loc ((v,e1)::nil) None e2 =>
      elift2
        (NNRCFor v)
        (ergoct_expr_to_nnrc env e1)
        (ergoct_expr_to_nnrc env e2)
    | EForeach (prov,_) _ _ _ =>
      complex_foreach_in_calculus_error prov (* XXX We should prove it never happens *)
    end.

  (** Translate a function to function+calculus *)
  Definition functionct_to_nnrc
             (fn:absolute_name)
             (f:ergoct_function) : eresult nnrc_function :=
    let env := List.map fst f.(functionct_sig).(sigc_params) in
    match f.(functionct_body) with
    | Some body =>
      elift
        (mkFuncN fn)
        (elift
           (mkLambdaN
              f.(functionct_sig).(sigc_params)
              f.(functionct_sig).(sigc_output))
           (ergoct_expr_to_nnrc env body))
    | None => function_not_inlined_error f.(functionct_annot) "ec2en/function" fn
    end.

  (** Translate a declaration to a declaration+calculus *)
  Definition clausect_declaration_to_nnrc
             (fn:absolute_name)
             (f:ergoct_function) : eresult nnrc_function :=
    functionct_to_nnrc fn f.

  (** Translate a contract to a contract+calculus *)
  (** For a contract, add 'contract' and 'now' to the translation_context *)
  Definition contractct_to_nnrc
             (cn:local_name)
             (c:ergoct_contract) : eresult nnrc_function_table :=
    let init := esuccess nil nil in
    let proc_one
          (acc:eresult (list nnrc_function))
          (s:absolute_name * ergoct_function)
        : eresult (list nnrc_function) :=
        eolift
          (fun acc : list nnrc_function =>
             elift (fun news : nnrc_function => news::acc)
                   (clausect_declaration_to_nnrc (fst s) (snd s)))
          acc
    in
    elift
      (mkFuncTableN cn)
      (List.fold_left proc_one c.(contractct_clauses) init).

  (** Translate a statement to a statement+calculus *)
  Definition declarationct_to_nnrc (s:ergoct_declaration) : eresult nnrc_declaration :=
    match s with
    | DCTExpr prov e =>
      elift
        DNExpr
        (ergoct_expr_to_nnrc nil e)
    | DCTConstant prov v _ e => (* Ignores the type annotation *)
      elift
        (DNConstant v) (* Add new variable to translation_context *)
        (ergoct_expr_to_nnrc nil e)
    | DCTFunc prov fn f =>
      elift
        DNFunc (* Add new function to translation_context *)
        (functionct_to_nnrc fn f)
    | DCTContract prov cn c =>
      elift DNFuncTable
            (contractct_to_nnrc cn c)
    end.

  (** Translate a module to a module+calculus *)
  Definition declarationsct_calculus_with_table (dl:list ergoct_declaration)
    : eresult (list nnrc_declaration) :=
    let init := esuccess nil nil in
    let proc_one
          (acc:eresult (list nnrc_declaration))
          (s:ergoct_declaration)
        : eresult (list nnrc_declaration) :=
        eolift
          (fun acc : list nnrc_declaration =>
             let edecl := declarationct_to_nnrc s in
             elift (fun news : nnrc_declaration => news::acc)
                   edecl)
          acc
    in
    List.fold_left proc_one dl init.

  (** Translate a module to a module+calculus *)
  Definition modulect_to_nnrc_with_table (p:ergoct_module) : eresult nnrc_module :=
    elift
      (mkModuleN p.(modulect_namespace))
      (declarationsct_calculus_with_table p.(modulect_declarations)).

  Definition ergoct_module_to_nnrc (m:ergoct_module) : eresult nnrc_module :=
    modulect_to_nnrc_with_table m.

  Section Examples.
    Open Scope string.
    Definition env0 : list string := nil.

    Definition typed_dummy_provenance : provenance * ergoc_type := (dummy_provenance, Unit).
    
    (**r Test pattern matching on values *)
    Definition input1 := dnat 2.

    Example j1 : ergoct_expr :=
      EMatch typed_dummy_provenance
             (EConst typed_dummy_provenance input1)
             ((CaseData typed_dummy_provenance (dnat 1), EConst typed_dummy_provenance (dstring "1"))
                :: (CaseData typed_dummy_provenance (dnat 2), EConst typed_dummy_provenance (dstring "2"))
                :: nil)
             (EConst typed_dummy_provenance (dstring "lots")).
    Definition jc1 := ergoct_expr_to_nnrc env0 j1.
    (* Compute jc1. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc1. *)

    Example j1' : ergoct_expr :=
      EMatch typed_dummy_provenance
             (EConst typed_dummy_provenance input1)
             ((CaseData typed_dummy_provenance (dnat 1), EConst typed_dummy_provenance (dstring "1"))
                :: (CaseLet typed_dummy_provenance "v2" None, EVar typed_dummy_provenance "v2")
                :: nil)
             (EConst typed_dummy_provenance (dstring "lots")).
    Definition jc1' := ergoct_expr_to_nnrc env0 j1'.
    (* Compute jc1'. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc1'. *)

    (**r Test pattern matching on type names *)
    Definition input2 :=
      dbrand ("C2"::nil) (dnat 1).
    
    Example j2 : ergoct_expr :=
      EMatch typed_dummy_provenance
             (EConst typed_dummy_provenance input2)
             ((CaseLet typed_dummy_provenance "v1" (Some "C1"), EConst typed_dummy_provenance (dstring "1"))
                :: (CaseLet typed_dummy_provenance "v2" (Some "C2"), EConst typed_dummy_provenance (dstring "2"))
                :: nil)
             (EConst typed_dummy_provenance (dstring "lots")).

    Definition jc2 := ergoct_expr_to_nnrc env0 j2.
    (* Compute jc2. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc2. *)

    (**r Test pattern matching on optional *)
    Definition input3 :=
      dsome (dnat 1).
    
    Definition input3none :=
      dnone.
    
    Example j3 input : ergoct_expr :=
      EMatch typed_dummy_provenance
             (EConst typed_dummy_provenance input)
             ((CaseLetOption typed_dummy_provenance "v1" None, EConst typed_dummy_provenance (dstring "1"))
                :: nil)
             (EConst typed_dummy_provenance (dstring "nothing")).

    Definition jc3 := ergoct_expr_to_nnrc env0 (j3 input3).
    Definition jc3none := ergoct_expr_to_nnrc env0 (j3 input3none).
    (* Compute jc3. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc3. *)
    (* Compute jc3none. *)
    (* Compute elift (fun x => nnrc_eval_top nil x nil) jc3none. *)

    Example j4 : ergoct_expr :=
      EForeach typed_dummy_provenance
               (("x", EConst typed_dummy_provenance (dcoll (dnat 1::dnat 2::dnat 3::nil)))
                  :: ("y", EConst typed_dummy_provenance (dcoll (dnat 4::dnat 5::dnat 6::nil)))
                  :: nil)
               None
               (ERecord typed_dummy_provenance
                        (("a",EVar typed_dummy_provenance "x")
                           ::("b",EVar typed_dummy_provenance "y")
                           ::nil)).
    Definition jc4 := ergoct_expr_to_nnrc env0 j4.
    (* Compute jc4. *)

    Example j5 : ergoct_expr :=
      EForeach typed_dummy_provenance
               (("x", EConst typed_dummy_provenance (dcoll (dnat 1::dnat 2::dnat 3::nil)))
                  :: ("y", EConst typed_dummy_provenance (dcoll (dnat 4::dnat 5::dnat 6::nil)))
                  :: nil)
               None
               (ENew typed_dummy_provenance
                     "person"
                     (("a",EVar typed_dummy_provenance "x")
                        ::("b",EVar typed_dummy_provenance "y")
                        ::nil)).
    Definition jc5 := ergoct_expr_to_nnrc env0 j5.
    (* Compute jc5. *)

  End Examples.

End ErgoCTtoErgoNNRC.

