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

Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Common.PrintTypedData.
Require Import ErgoSpec.Types.ErgoCTypeUtil.
Require Import ErgoSpec.Types.ErgoTypetoErgoCType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCOverloaded.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheckContext.

Section ErgoCTypecheck.
  Context {m : brand_model}.

  Import ErgoCType.

  Fixpoint ergoc_typecheck_expr nsctxt (ctxt : type_context) (expr : ergoc_expr) : eresult ergoct_expr :=
    match expr with
    | EThisContract prov => efailure (ESystemError prov "No `this' in ergoc")
    | EThisClause   prov => efailure (ESystemError prov "No `clause' in ergoc")
    | EThisState    prov => efailure (ESystemError prov "No `state' in ergoc")
    | EVar prov name =>
      let opt := lookup String.string_dec (ctxt.(type_context_local_env)++ctxt.(type_context_global_env)) name in
      let topt := eresult_of_option opt (ETypeError prov ("Variable `" ++ name ++ "' not found.")%string) nil in
      elift (fun T => EVar (prov,T) name) topt
    | EConst prov d =>
      let topt := eresult_of_option (infer_data_type d) (ETypeError prov "Bad constant.") nil in
      elift (fun T => EConst (prov,T) d) topt
    | ENone prov => esuccess (ENone (prov, toption tbottom)) nil
    | ESome prov e =>
      elift (fun eT => ESome (prov,toption (exprct_type_annot eT)) eT) (ergoc_typecheck_expr nsctxt ctxt e)
    | EArray prov es =>
      elift (fun eT => EArray (prov,tcoll (snd eT)) (fst eT))
            (fold_right
               (fun (new:ergoc_expr) (eT:eresult (list ergoct_expr * ergoc_type)) =>
                  eolift
                    (fun (eT':list ergoct_expr * ergoc_type) =>
                       elift
                         (fun (new':ergoct_expr) =>
                            (new'::(fst eT'), ergoc_type_join (exprct_type_annot new') (snd eT')))
                         (ergoc_typecheck_expr nsctxt ctxt new))
                    eT)
               (esuccess (nil,tbottom) nil) es)
    | EUnaryOperator prov eop e =>
      eolift (unary_dispatch nsctxt prov eop)
             (ergoc_typecheck_expr nsctxt ctxt e)
    | EBinaryOperator prov eop e1 e2 =>
      eolift2 (binary_dispatch nsctxt prov eop)
              (ergoc_typecheck_expr nsctxt ctxt e1)
              (ergoc_typecheck_expr nsctxt ctxt e2)
    | EUnaryBuiltin prov op e =>
      eolift
        (fun eT =>
           let t := exprct_type_annot eT in
           match ergoc_type_infer_unary_op op t with
           | Some (r, _) => esuccess (EUnaryBuiltin (prov,r) op eT) nil
           | None => efailure (ETypeError prov (ergo_format_unop_error nsctxt op t))
           end)
        (ergoc_typecheck_expr nsctxt ctxt e)
    | EBinaryBuiltin prov op e1 e2 =>
      eolift2
        (fun eT1 eT2 =>
          let t1 := exprct_type_annot eT1 in
          let t2 := exprct_type_annot eT2 in
          match ergoc_type_infer_binary_op op t1 t2 with
          | Some (r, _, _) => esuccess (EBinaryBuiltin (prov,r) op eT1 eT2) nil
          | None => efailure (ETypeError prov (ergo_format_binop_error nsctxt op t1 t2))
          end)
        (ergoc_typecheck_expr nsctxt ctxt e1)
        (ergoc_typecheck_expr nsctxt ctxt e2)
    | EIf prov c t f =>
      eolift (fun cT' =>
                if ergoc_type_subtype_dec (exprct_type_annot cT') tbool then
                  elift2 (fun eT1 eT2 =>
                            let t1 := exprct_type_annot eT1 in
                            let t2 := exprct_type_annot eT2 in
                            EIf (prov,ergoc_type_join t1 t2) cT' eT1 eT2)
                         (ergoc_typecheck_expr nsctxt ctxt t)
                         (ergoc_typecheck_expr nsctxt ctxt f)
                else efailure (ETypeError (expr_annot c) "'if' condition not boolean."%string))
             (ergoc_typecheck_expr nsctxt ctxt c)
    | ELet prov n None v e =>
      (eolift (fun evT =>
                 let vt := exprct_type_annot evT in
                 let ctxt' := type_context_update_local_env ctxt n vt in
                 elift (fun eT => ELet (prov, exprct_type_annot eT) n None evT eT)
                       (ergoc_typecheck_expr nsctxt ctxt' e))
              (ergoc_typecheck_expr nsctxt ctxt v))
    | ELet prov n (Some t) v e  =>
      let fmt_err :=
          fun t' vt =>
          match prov with
          | ProvFunc _ fname =>
            ETypeError prov
                       ("Function `" ++ fname
                                     ++ "' expected argument `"
                                     ++ n
                                     ++ "' to be of type `"
                                     ++ (ergoc_type_to_string nsctxt t')
                                     ++ "' but was given argument of type `"
                                     ++ (ergoc_type_to_string nsctxt vt)
                                     ++ "'." )
          | _ => ETypeError prov
                            ("The let type annotation `"
                               ++ (ergoc_type_to_string nsctxt t')
                               ++ "' for the name `"
                               ++ n
                               ++ "' does not match the actual type `"
                               ++ (ergoc_type_to_string nsctxt vt)
                               ++ "'.")
          end
      in
      (eolift
         (fun evT =>
            let vt := exprct_type_annot evT in
            let t' := (ergo_type_to_ergoc_type t) in
            if subtype_dec vt t' then
              let ctxt' :=
                  type_context_update_local_env
                    ctxt n
                    t'
              in
              elift (fun eT => ELet (prov, exprct_type_annot eT) n (Some t) evT eT)
                    (ergoc_typecheck_expr nsctxt ctxt' e)
            else
              efailure (fmt_err t' vt))
         (ergoc_typecheck_expr nsctxt ctxt v))
    | EPrint prov v e =>
      print_in_calculus_error prov
    | ERecord prov rs =>
      elift (fun eT => ERecord (prov,(snd eT)) (fst eT))
            (fold_right
               (fun (next:string * ergoc_expr) (sofar:eresult (list (string * ergoct_expr) * ergoc_type)) =>
                  eolift2
                    (fun (sofar':list (string * ergoct_expr) * ergoc_type)
                         (next':(string * ergoct_expr) * ergoc_type) =>
                       elift (fun T' => (fst next'::fst sofar',compose fst fst T'))
                             (eresult_of_option
                                (ergoc_type_infer_binary_op OpRecConcat (snd next') (snd sofar'))
                                (ETypeError prov "Bad record! Failed to concat."%string) nil))
                    sofar
                    (eolift (fun efT =>
                               let ft := exprct_type_annot efT in
                               elift (fun T => ((fst next,efT), fst T))
                                     (eresult_of_option
                                        (ergoc_type_infer_unary_op (OpRec (fst next)) ft)
                                        (ETypeError prov "Bad record! Failed to init."%string) nil))
                            (ergoc_typecheck_expr nsctxt ctxt (snd next))))
               (esuccess (nil,empty_rec_type) nil) rs)
    | ENew prov name rs =>
      eolift
        (fun rsT' =>
           elift (fun T'' => ENew (prov, fst T'') name (fst rsT'))
                 (eresult_of_option
                    (infer_brand_strict (name::nil) (snd rsT'))
                    (ETypeError prov (ergo_format_new_error nsctxt name (snd rsT'))) nil))
        (fold_right
           (fun (next:string * ergoc_expr) (sofar:eresult (list (string * ergoct_expr) * ergoc_type)) =>
              eolift2
                (fun (sofar':list (string * ergoct_expr) * ergoc_type)
                     (next':(string * ergoct_expr) * ergoc_type) =>
                   elift (fun T' => (fst next'::fst sofar',compose fst fst T'))
                         (eresult_of_option
                            (ergoc_type_infer_binary_op OpRecConcat (snd next') (snd sofar'))
                            (ETypeError prov "Bad record! Failed to concat."%string) nil))
                sofar
                (eolift (fun efT =>
                           let ft := exprct_type_annot efT in
                           elift (fun T => ((fst next,efT), fst T))
                                 (eresult_of_option
                                    (ergoc_type_infer_unary_op (OpRec (fst next)) ft)
                                    (ETypeError prov "Bad record! Failed to init."%string) nil))
                        (ergoc_typecheck_expr nsctxt ctxt (snd next))))
           (esuccess (nil,empty_rec_type) nil) rs)
    | ECallFun prov fname args => function_not_inlined_error prov "typing" fname
    | ECallFunInGroup prov gname fname args => function_in_group_not_inlined_error prov gname fname
    | EMatch prov term pes default =>
      eolift2
        (fun eT0 dT =>
          let t0 := exprct_type_annot eT0 in
          let dt := exprct_type_annot dT in
          elift
            (fun ecasesT =>
               EMatch (prov, snd ecasesT)
                      eT0
                      (fst ecasesT)
                      dT)
            (fold_right
               (fun pe sofarT =>
                  match pe with
                  | (CaseData prov d, res) => (* TODO can `d' ever be bad? *)
                    match ergoc_type_infer_data d with
                    | None => efailure (ETypeError prov "Ill-typed data literal!")
                    | Some dt =>
                      elift2 (fun sofarT eT =>
                                let et := exprct_type_annot eT in
                                let sofart := ergoc_type_join et (snd sofarT) in
                                ((CaseData (prov,sofart) d,eT)::fst sofarT, sofart))
                             sofarT
                             (ergoc_typecheck_expr nsctxt ctxt res)
                    end
                  | (CaseWildcard prov None, res) =>
                    elift2 (fun sofarT eT =>
                              let et := exprct_type_annot eT in
                              let sofart := ergoc_type_join et (snd sofarT) in
                              ((CaseWildcard (prov,sofart) None,eT)::fst sofarT, sofart))
                           sofarT
                           (ergoc_typecheck_expr nsctxt ctxt res)
                  | (CaseLet prov name None, res) =>
                    elift2 (fun sofarT eT =>
                              let et := exprct_type_annot eT in
                              let sofart := ergoc_type_join et (snd sofarT) in
                              ((CaseLet (prov,sofart) name None,eT)::fst sofarT, sofart))
                           sofarT
                           (ergoc_typecheck_expr nsctxt (type_context_update_local_env ctxt name t0) res)
                  | (CaseLetOption prov name None, res) =>
                    match unteither t0 with
                    | None =>
                      case_option_not_on_either_error prov
                    | Some (st, ft) =>
                      elift2 (fun sofarT eT =>
                                let et := exprct_type_annot eT in
                                let sofart := ergoc_type_join et (snd sofarT) in
                                ((CaseLetOption (prov,sofart) name None,eT)::fst sofarT, sofart))
                             sofarT
                             (ergoc_typecheck_expr nsctxt (type_context_update_local_env ctxt name st) res)
                    end
                  | (CaseLetOption prov name (Some b), res) =>
                    match unteither t0 with
                    | None =>
                      case_option_not_on_either_error prov
                    | Some (st, ft) =>
                      elift2 (fun sofarT eT =>
                                let sofart := snd sofarT in
                                ((CaseLetOption (prov,sofart) name (Some b), eT)::fst sofarT, sofart))
                             sofarT
                             (ergoc_typecheck_expr
                                nsctxt (type_context_update_local_env
                                          ctxt
                                          name
                                          (tbrand (b::nil)))
                                res)
                    end
                  | (CaseWildcard prov (Some b), res) =>
                    elift2 (fun sofarT eT =>
                              let sofart := snd sofarT in
                              ((CaseWildcard (prov,sofart) (Some b), eT)::fst sofarT, sofart))
                           sofarT
                           (ergoc_typecheck_expr nsctxt ctxt res)
                  | (CaseLet prov name (Some b), res) =>
                    elift2 (fun sofarT eT =>
                              let sofart := snd sofarT in
                              ((CaseLet (prov,sofart) name (Some b), eT)::fst sofarT, sofart))
                           sofarT
                           (ergoc_typecheck_expr
                              nsctxt
                              (type_context_update_local_env
                                 ctxt
                                 name
                                 (tbrand (b::nil)))
                              res)
                  end)
               (esuccess (nil, dt) nil)
               pes))
        (ergoc_typecheck_expr nsctxt ctxt term)
        (ergoc_typecheck_expr nsctxt ctxt default)
    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach prov ((name,arr)::nil) None fn =>
      eolift
        (fun arrT' =>
           let arr' := exprct_type_annot arrT' in
           eolift
             (fun typ =>
                (elift
                   (fun eT => EForeach (prov, tcoll (exprct_type_annot eT)) ((name,arrT')::nil) None eT)
                   (ergoc_typecheck_expr nsctxt (type_context_update_local_env ctxt name typ) fn)))
             (eresult_of_option
                (untcoll arr')
                (ETypeError
                   prov
                   ("foreach expects an array to iterate over, but was given something of type `" ++ (ergoc_type_to_string nsctxt arr') ++ "'.")) nil))
        (ergoc_typecheck_expr nsctxt ctxt arr)
    | EForeach prov _ _ _ =>
      complex_foreach_in_calculus_error prov
    end.

  Definition ergoc_typecheck_function
             (nsctxt: namespace_ctxt)
             (name:string)
             (dctxt : type_context)
             (func : ergoc_function) : eresult (ergoct_function * type_context) :=
    match func.(functionc_body) with
    | None => esuccess (mkFuncCT
                          func.(functionc_annot)
                          func.(functionc_sig)
                          None,
                        dctxt) nil
    | Some body =>
      let tsig :=
          map (fun x => (fst x, ergo_type_to_ergoc_type (snd x)))
              func.(functionc_sig).(sigc_params) in
      eolift
        (fun outT =>
           let outt := exprct_type_annot outT in
           let eoutt := func.(functionc_sig).(sigc_output) in
           match eoutt with
           | None => esuccess (mkFuncCT
                                 func.(functionc_annot)
                                 func.(functionc_sig)
                                 (Some outT),
                               dctxt) nil
           | Some eoutt' =>
             let expectedt := ergo_type_to_ergoc_type eoutt' in
             if subtype_dec outt expectedt
             then esuccess (mkFuncCT
                              func.(functionc_annot)
                              func.(functionc_sig)
                              (Some outT),
                            dctxt) nil
             else
               let body_prov := bodyc_annot func in
               match func.(functionc_annot) with
               | ProvClause _ name =>
                 efailure (ETypeError body_prov (ergo_format_clause_return_error nsctxt name outt expectedt))
               | ProvFunc _ name =>
                 efailure (ETypeError body_prov (ergo_format_function_return_error nsctxt name outt expectedt))
               | _ =>
                 efailure (ETypeError body_prov (ergo_format_function_return_error nsctxt name outt expectedt))
               end
           end)
        (ergoc_typecheck_expr nsctxt (type_context_set_local_env dctxt tsig) body)
    end.

  Definition ergoc_typecheck_clause
             (nsctxt: namespace_ctxt)
             (dctxt : type_context)
             (cl : string * ergoc_function) : eresult ((string * ergoct_function) * type_context) :=
    let (name,body) := cl in
    elift (fun fT => ((name,fst fT), snd fT)) (ergoc_typecheck_function nsctxt name dctxt body).

  Definition ergoc_typecheck_contract
             (nsctxt: namespace_ctxt)
             (dctxt : type_context)
             (coname: absolute_name)
             (c : ergoc_contract) : eresult (ergoct_contract * type_context) :=
    elift (fun cT =>
             (mkContractCT
                c.(contractc_annot)
                (fst cT),
              snd cT))
          (elift_context_fold_left
             (ergoc_typecheck_clause nsctxt)
             c.(contractc_clauses)
             dctxt).

  Definition ergoc_typecheck_decl
             (nsctxt: namespace_ctxt)
             (dctxt : type_context)
             (decl : ergoc_declaration)
    : eresult (ergoct_declaration * type_context) :=
    match decl with
    | DCExpr prov expr =>
      let exprT := ergoc_typecheck_expr nsctxt dctxt expr in
      elift (fun xT => (DCTExpr (prov, exprct_type_annot xT) xT, dctxt)) exprT
    | DCConstant prov name None expr =>
      let exprT := ergoc_typecheck_expr nsctxt dctxt expr in
      elift (fun xT => (DCTConstant (prov,exprct_type_annot xT) name None xT,
                        type_context_update_global_env dctxt name (exprct_type_annot xT)))
            exprT
    | DCConstant prov name (Some t) expr =>
      let fmt_err :=
          fun t' vt =>
            ETypeError prov
                       ("The type annotation `"
                          ++ (ergoc_type_to_string nsctxt t')
                          ++ "' for the constant `"
                          ++ name
                          ++ "' does not match its actual type `"
                          ++ (ergoc_type_to_string nsctxt vt)
                          ++ "'.")
      in
      let exprT := ergoc_typecheck_expr nsctxt dctxt expr in
      eolift
        (fun vT =>
           let vt := exprct_type_annot vT in
           let t' := (ergo_type_to_ergoc_type t) in
           if subtype_dec vt t' then
             let ctxt' := type_context_update_global_env dctxt name t' in
             esuccess (DCTConstant (prov,t') name (Some t) vT, ctxt') nil
           else
             efailure (fmt_err t' vt))
        exprT
    | DCFunc prov name func =>
      elift (fun fc => (DCTFunc prov name (fst fc),snd fc))
            (ergoc_typecheck_function nsctxt name dctxt func)
    | DCContract prov name contr =>
      elift (fun fc => (DCTContract prov name (fst fc),snd fc))
            (ergoc_typecheck_contract nsctxt dctxt name contr)
    end.

  Definition ergoc_typecheck_module
             (nsctxt: namespace_ctxt)
             (dctxt : type_context)
             (mod : ergoc_module)
    : eresult (ergoct_module * type_context) :=
    elift (fun x => (mkModuleCT
                       mod.(modulec_annot)
                       mod.(modulec_namespace)
                      (fst x),
                     snd x))
          (elift_context_fold_left
             (ergoc_typecheck_decl nsctxt)
             mod.(modulec_declarations)
             dctxt).
  
End ErgoCTypecheck.
