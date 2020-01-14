open Assoc
open Ast
open Basics
open BinaryOperators
open Datatypes
open Ergo
open ErgoC
open ErgoCOverloaded
open ErgoCT
open ErgoCTypecheckContext
open ErgoTypetoQcertType
open List0
open Names
open NamespaceContext
open PrintTypedData
open Provenance
open QcertData
open QcertDataTyping
open QcertType
open QcertTypeUtil
open RSubtype
open Result0
open String0
open TBrandModel
open TDataInfer
open UnaryOperators

(** val ergoc_expr_typecheck :
    brand_model -> namespace_ctxt -> type_context -> ergoc_expr ->
    ergoct_expr eresult **)

let rec ergoc_expr_typecheck m nsctxt ctxt = function
| EThis prov -> this_in_calculus_error prov
| EThisContract prov -> contract_in_calculus_error prov
| EThisClause prov -> clause_in_calculus_error prov
| EThisState prov -> state_in_calculus_error prov
| EVar (prov, name) ->
  let opt =
    lookup string_dec
      (app ctxt.type_context_local_env ctxt.type_context_global_env) name
  in
  let topt =
    eresult_of_option opt (ETypeError (prov,
      (append
        ('V'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('`'::[]))))))))))
        (append name
          ('\''::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::('.'::[]))))))))))))))))
      []
  in
  elift (fun t -> EVar ((prov, t), name)) topt
| EConst (prov, d) ->
  let topt =
    eresult_of_option
      (infer_data_type enhanced_foreign_data enhanced_foreign_type
        enhanced_foreign_data_typing m d) (ETypeError (prov,
      ('B'::('a'::('d'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::('.'::[])))))))))))))))
      []
  in
  elift (fun t -> EConst ((prov, t), d)) topt
| EText (prov, _) -> text_in_calculus_error prov
| ENone prov ->
  esuccess (ENone (prov,
    (QLib.QcertType.toption m.brand_model_relation
      (QLib.QcertType.tbottom m.brand_model_relation)))) []
| ESome (prov, e) ->
  elift (fun eT -> ESome ((prov,
    (QLib.QcertType.toption m.brand_model_relation (exprct_type_annot m eT))),
    eT)) (ergoc_expr_typecheck m nsctxt ctxt e)
| EArray (prov, es) ->
  elift (fun eT -> EArray ((prov,
    (QLib.QcertType.tcoll m.brand_model_relation (snd eT))), (fst eT)))
    (fold_right (fun new0 eT ->
      eolift (fun eT' ->
        elift (fun new' -> ((new' :: (fst eT')),
          (QLib.QcertType.qcert_type_join m.brand_model_relation
            (exprct_type_annot m new') (snd eT'))))
          (ergoc_expr_typecheck m nsctxt ctxt new0)) eT)
      (esuccess ([], (QLib.QcertType.tbottom m.brand_model_relation)) []) es)
| EUnaryOperator (prov, eop, e) ->
  eolift (unary_dispatch m nsctxt prov eop)
    (ergoc_expr_typecheck m nsctxt ctxt e)
| EBinaryOperator (prov, eop, e1, e2) ->
  eolift2 (binary_dispatch m nsctxt prov eop)
    (ergoc_expr_typecheck m nsctxt ctxt e1)
    (ergoc_expr_typecheck m nsctxt ctxt e2)
| EUnaryBuiltin (prov, op, e) ->
  eolift (fun eT ->
    let t = exprct_type_annot m eT in
    (match QLib.QcertType.qcert_type_infer_unary_op m op t with
     | Some p ->
       let (r, _) = p in esuccess (EUnaryBuiltin ((prov, r), op, eT)) []
     | None ->
       efailure (ETypeError (prov, (ergo_format_unop_error m nsctxt op t)))))
    (ergoc_expr_typecheck m nsctxt ctxt e)
| EBinaryBuiltin (prov, op, e1, e2) ->
  eolift2 (fun eT1 eT2 ->
    let t1 = exprct_type_annot m eT1 in
    let t2 = exprct_type_annot m eT2 in
    (match QLib.QcertType.qcert_type_infer_binary_op m op t1 t2 with
     | Some p ->
       let (p0, _) = p in
       let (r, _) = p0 in
       esuccess (EBinaryBuiltin ((prov, r), op, eT1, eT2)) []
     | None ->
       efailure (ETypeError (prov,
         (ergo_format_binop_error m nsctxt op t1 t2)))))
    (ergoc_expr_typecheck m nsctxt ctxt e1)
    (ergoc_expr_typecheck m nsctxt ctxt e2)
| EIf (prov, c, t, f) ->
  eolift (fun cT' ->
    if QLib.QcertType.qcert_type_subtype_dec m (exprct_type_annot m cT')
         (QLib.QcertType.tbool m.brand_model_relation)
    then elift2 (fun eT1 eT2 ->
           let t1 = exprct_type_annot m eT1 in
           let t2 = exprct_type_annot m eT2 in
           EIf ((prov,
           (QLib.QcertType.qcert_type_join m.brand_model_relation t1 t2)),
           cT', eT1, eT2)) (ergoc_expr_typecheck m nsctxt ctxt t)
           (ergoc_expr_typecheck m nsctxt ctxt f)
    else efailure (ETypeError ((expr_annot c),
           ('\''::('i'::('f'::('\''::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('b'::('o'::('o'::('l'::('e'::('a'::('n'::('.'::[]))))))))))))))))))))))))))))))
    (ergoc_expr_typecheck m nsctxt ctxt c)
| ELet (prov, n, o, v, e) ->
  (match o with
   | Some t ->
     let fmt_err = fun t' vt ->
       match prov with
       | ProvFunc (_, fname) ->
         ETypeError (prov,
           (append
             ('F'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('`'::[]))))))))))
             (append fname
               (append
                 ('\''::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('`'::[])))))))))))))))))))))
                 (append n
                   (append
                     ('\''::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))
                     (append (qcert_type_to_string m nsctxt t')
                       (append
                         ('\''::(' '::('b'::('u'::('t'::(' '::('w'::('a'::('s'::(' '::('g'::('i'::('v'::('e'::('n'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))))))))))))
                         (append (qcert_type_to_string m nsctxt vt)
                           ('\''::('.'::[])))))))))))
       | _ ->
         ETypeError (prov,
           (append
             ('T'::('h'::('e'::(' '::('l'::('e'::('t'::(' '::('t'::('y'::('p'::('e'::(' '::('a'::('n'::('n'::('o'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('`'::[])))))))))))))))))))))))))
             (append (qcert_type_to_string m nsctxt t')
               (append
                 ('\''::(' '::('f'::('o'::('r'::(' '::('t'::('h'::('e'::(' '::('n'::('a'::('m'::('e'::(' '::('`'::[]))))))))))))))))
                 (append n
                   (append
                     ('\''::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('t'::('h'::('e'::(' '::('a'::('c'::('t'::('u'::('a'::('l'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))))))))))))
                     (append (qcert_type_to_string m nsctxt vt)
                       ('\''::('.'::[])))))))))
     in
     eolift (fun evT ->
       let vt = exprct_type_annot m evT in
       let t' = ergo_type_to_qcert_type m.brand_model_relation t in
       if subtype_dec enhanced_foreign_type m.brand_model_relation vt t'
       then let ctxt' =
              type_context_update_local_env m.brand_model_relation ctxt n t'
            in
            elift (fun eT -> ELet ((prov, (exprct_type_annot m eT)), n, (Some
              t), evT, eT)) (ergoc_expr_typecheck m nsctxt ctxt' e)
       else efailure (fmt_err t' vt)) (ergoc_expr_typecheck m nsctxt ctxt v)
   | None ->
     eolift (fun evT ->
       let vt = exprct_type_annot m evT in
       let ctxt' =
         type_context_update_local_env m.brand_model_relation ctxt n vt
       in
       elift (fun eT -> ELet ((prov, (exprct_type_annot m eT)), n, None, evT,
         eT)) (ergoc_expr_typecheck m nsctxt ctxt' e))
       (ergoc_expr_typecheck m nsctxt ctxt v))
| EPrint (prov, _, _) -> print_in_calculus_error prov
| ERecord (prov, rs) ->
  elift (fun eT -> ERecord ((prov, (snd eT)), (fst eT)))
    (fold_right (fun next sofar ->
      eolift2 (fun sofar' next' ->
        elift (fun t' -> (((fst next') :: (fst sofar')),
          (compose fst fst t')))
          (eresult_of_option
            (QLib.QcertType.qcert_type_infer_binary_op m OpRecConcat
              (snd next') (snd sofar')) (ETypeError (prov,
            ('B'::('a'::('d'::(' '::('r'::('e'::('c'::('o'::('r'::('d'::('!'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('t'::('o'::(' '::('c'::('o'::('n'::('c'::('a'::('t'::('.'::[])))))))))))))))))))))))))))))))
            [])) sofar
        (eolift (fun efT ->
          let ft = exprct_type_annot m efT in
          elift (fun t -> (((fst next), efT), (fst t)))
            (eresult_of_option
              (QLib.QcertType.qcert_type_infer_unary_op m (OpRec (fst next))
                ft) (ETypeError (prov,
              ('B'::('a'::('d'::(' '::('r'::('e'::('c'::('o'::('r'::('d'::('!'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('t'::('o'::(' '::('i'::('n'::('i'::('t'::('.'::[])))))))))))))))))))))))))))))
              [])) (ergoc_expr_typecheck m nsctxt ctxt (snd next))))
      (esuccess ([], (empty_rec_type m)) []) rs)
| ENew (prov, name, rs) ->
  eolift (fun rsT' ->
    elift (fun t'' -> ENew ((prov, (fst t'')), name, (fst rsT')))
      (eresult_of_option
        (QLib.QcertType.infer_brand_strict m (name :: []) (snd rsT'))
        (ETypeError (prov, (ergo_format_new_error m nsctxt name (snd rsT'))))
        []))
    (fold_right (fun next sofar ->
      eolift2 (fun sofar' next' ->
        elift (fun t' -> (((fst next') :: (fst sofar')),
          (compose fst fst t')))
          (eresult_of_option
            (QLib.QcertType.qcert_type_infer_binary_op m OpRecConcat
              (snd next') (snd sofar')) (ETypeError (prov,
            ('B'::('a'::('d'::(' '::('r'::('e'::('c'::('o'::('r'::('d'::('!'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('t'::('o'::(' '::('c'::('o'::('n'::('c'::('a'::('t'::('.'::[])))))))))))))))))))))))))))))))
            [])) sofar
        (eolift (fun efT ->
          let ft = exprct_type_annot m efT in
          elift (fun t -> (((fst next), efT), (fst t)))
            (eresult_of_option
              (QLib.QcertType.qcert_type_infer_unary_op m (OpRec (fst next))
                ft) (ETypeError (prov,
              ('B'::('a'::('d'::(' '::('r'::('e'::('c'::('o'::('r'::('d'::('!'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('t'::('o'::(' '::('i'::('n'::('i'::('t'::('.'::[])))))))))))))))))))))))))))))
              [])) (ergoc_expr_typecheck m nsctxt ctxt (snd next))))
      (esuccess ([], (empty_rec_type m)) []) rs)
| ECallFun (prov, fname, _) ->
  function_not_inlined_error prov
    ('t'::('y'::('p'::('i'::('n'::('g'::[])))))) fname
| ECallFunInGroup (prov, gname, fname, _) ->
  function_in_group_not_inlined_error prov gname fname
| EMatch (prov, term, pes, default) ->
  eolift2 (fun eT0 dT ->
    let t0 = exprct_type_annot m eT0 in
    let dt = exprct_type_annot m dT in
    elift (fun ecasesT -> EMatch ((prov, (snd ecasesT)), eT0, (fst ecasesT),
      dT))
      (fold_right (fun pe sofarT ->
        let (y, res) = pe in
        (match y with
         | CaseData (prov0, d) ->
           (match QLib.QcertType.qcert_type_infer_data m d with
            | Some _ ->
              elift2 (fun sofarT0 eT ->
                let et = exprct_type_annot m eT in
                let sofart =
                  QLib.QcertType.qcert_type_join m.brand_model_relation et
                    (snd sofarT0)
                in
                ((((CaseData ((prov0, sofart), d)), eT) :: (fst sofarT0)),
                sofart)) sofarT (ergoc_expr_typecheck m nsctxt ctxt res)
            | None ->
              efailure (ETypeError (prov0,
                ('I'::('l'::('l'::('-'::('t'::('y'::('p'::('e'::('d'::(' '::('d'::('a'::('t'::('a'::(' '::('l'::('i'::('t'::('e'::('r'::('a'::('l'::('!'::[]))))))))))))))))))))))))))
         | CaseEnum (prov0, name) ->
           let opt =
             lookup string_dec
               (app ctxt.type_context_local_env ctxt.type_context_global_env)
               name
           in
           let topt =
             eresult_of_option opt (ETypeError (prov0,
               (append ('E'::('n'::('u'::('m'::(' '::('`'::[]))))))
                 (append name
                   ('\''::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::('.'::[]))))))))))))))))
               []
           in
           eolift (fun _ ->
             elift2 (fun sofarT0 eT ->
               let et = exprct_type_annot m eT in
               let sofart =
                 QLib.QcertType.qcert_type_join m.brand_model_relation et
                   (snd sofarT0)
               in
               ((((CaseEnum ((prov0, sofart), name)), eT) :: (fst sofarT0)),
               sofart)) sofarT (ergoc_expr_typecheck m nsctxt ctxt res)) topt
         | CaseWildcard (prov0, t) ->
           (match t with
            | Some b ->
              elift2 (fun sofarT0 eT ->
                let sofart = snd sofarT0 in
                ((((CaseWildcard ((prov0, sofart), (Some b))),
                eT) :: (fst sofarT0)), sofart)) sofarT
                (ergoc_expr_typecheck m nsctxt ctxt res)
            | None ->
              elift2 (fun sofarT0 eT ->
                let et = exprct_type_annot m eT in
                let sofart =
                  QLib.QcertType.qcert_type_join m.brand_model_relation et
                    (snd sofarT0)
                in
                ((((CaseWildcard ((prov0, sofart), None)),
                eT) :: (fst sofarT0)), sofart)) sofarT
                (ergoc_expr_typecheck m nsctxt ctxt res))
         | CaseLet (prov0, name, t) ->
           (match t with
            | Some b ->
              elift2 (fun sofarT0 eT ->
                let et = exprct_type_annot m eT in
                let sofart =
                  QLib.QcertType.qcert_type_join m.brand_model_relation et
                    (snd sofarT0)
                in
                ((((CaseLet ((prov0, sofart), name, (Some b))),
                eT) :: (fst sofarT0)), sofart)) sofarT
                (ergoc_expr_typecheck m nsctxt
                  (type_context_update_local_env m.brand_model_relation ctxt
                    name
                    (QLib.QcertType.tbrand m.brand_model_relation (b :: [])))
                  res)
            | None ->
              elift2 (fun sofarT0 eT ->
                let et = exprct_type_annot m eT in
                let sofart =
                  QLib.QcertType.qcert_type_join m.brand_model_relation et
                    (snd sofarT0)
                in
                ((((CaseLet ((prov0, sofart), name, None)),
                eT) :: (fst sofarT0)), sofart)) sofarT
                (ergoc_expr_typecheck m nsctxt
                  (type_context_update_local_env m.brand_model_relation ctxt
                    name t0) res))
         | CaseLetOption (prov0, name, t) ->
           (match t with
            | Some b ->
              (match QLib.QcertType.unteither m t0 with
               | Some _ ->
                 elift2 (fun sofarT0 eT ->
                   let et = exprct_type_annot m eT in
                   let sofart =
                     QLib.QcertType.qcert_type_join m.brand_model_relation et
                       (snd sofarT0)
                   in
                   ((((CaseLetOption ((prov0, sofart), name, (Some b))),
                   eT) :: (fst sofarT0)), sofart)) sofarT
                   (ergoc_expr_typecheck m nsctxt
                     (type_context_update_local_env m.brand_model_relation
                       ctxt name
                       (QLib.QcertType.tbrand m.brand_model_relation
                         (b :: []))) res)
               | None -> case_option_not_on_either_error prov0)
            | None ->
              (match QLib.QcertType.unteither m t0 with
               | Some p ->
                 let (st, _) = p in
                 elift2 (fun sofarT0 eT ->
                   let et = exprct_type_annot m eT in
                   let sofart =
                     QLib.QcertType.qcert_type_join m.brand_model_relation et
                       (snd sofarT0)
                   in
                   ((((CaseLetOption ((prov0, sofart), name, None)),
                   eT) :: (fst sofarT0)), sofart)) sofarT
                   (ergoc_expr_typecheck m nsctxt
                     (type_context_update_local_env m.brand_model_relation
                       ctxt name st) res)
               | None -> case_option_not_on_either_error prov0))))
        (esuccess ([], dt) []) pes))
    (ergoc_expr_typecheck m nsctxt ctxt term)
    (ergoc_expr_typecheck m nsctxt ctxt default)
| EForeach (prov, l, o, fn) ->
  (match l with
   | [] -> complex_foreach_in_calculus_error prov
   | p :: l0 ->
     let (name, arr) = p in
     (match l0 with
      | [] ->
        (match o with
         | Some _ -> complex_foreach_in_calculus_error prov
         | None ->
           eolift (fun arrT' ->
             let arr' = exprct_type_annot m arrT' in
             eolift (fun typ ->
               elift (fun eT -> EForeach ((prov,
                 (QLib.QcertType.tcoll m.brand_model_relation
                   (exprct_type_annot m eT))), ((name, arrT') :: []), None,
                 eT))
                 (ergoc_expr_typecheck m nsctxt
                   (type_context_update_local_env m.brand_model_relation ctxt
                     name typ) fn))
               (eresult_of_option (QLib.QcertType.untcoll m arr') (ETypeError
                 (prov,
                 (append
                   ('f'::('o'::('r'::('e'::('a'::('c'::('h'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('s'::(' '::('a'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('t'::('o'::(' '::('i'::('t'::('e'::('r'::('a'::('t'::('e'::(' '::('o'::('v'::('e'::('r'::(','::(' '::('b'::('u'::('t'::(' '::('w'::('a'::('s'::(' '::('g'::('i'::('v'::('e'::('n'::(' '::('s'::('o'::('m'::('e'::('t'::('h'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   (append (qcert_type_to_string m nsctxt arr')
                     ('\''::('.'::[])))))) []))
             (ergoc_expr_typecheck m nsctxt ctxt arr))
      | _ :: _ -> complex_foreach_in_calculus_error prov))
| EAs (prov, f, e) ->
  eolift (as_dispatch m nsctxt prov f) (ergoc_expr_typecheck m nsctxt ctxt e)

(** val ergoc_function_typecheck :
    brand_model -> namespace_ctxt -> char list -> type_context ->
    ergoc_function -> (ergoct_function * type_context) eresult **)

let ergoc_function_typecheck m nsctxt name dctxt func =
  match func.functionc_body with
  | Some body ->
    let tparams =
      map (fun x -> ((fst x),
        (ergo_type_to_qcert_type m.brand_model_relation (snd x))))
        func.functionc_sig.sigc_params
    in
    eolift (fun outT ->
      let outt = exprct_type_annot m outT in
      let eoutt = func.functionc_sig.sigc_output in
      (match eoutt with
       | Some eoutt' ->
         let expectedt = ergo_type_to_qcert_type m.brand_model_relation eoutt'
         in
         if subtype_dec enhanced_foreign_type m.brand_model_relation outt
              expectedt
         then esuccess ({ functionct_annot = func.functionc_annot;
                functionct_sig = { sigct_params = tparams; sigct_output =
                expectedt }; functionct_body = (Some outT) }, dctxt) []
         else let body_prov = bodyc_annot func in
              (match func.functionc_annot with
               | ProvFunc (_, name0) ->
                 efailure (ETypeError (body_prov,
                   (ergo_format_function_return_error m nsctxt name0 outt
                     expectedt)))
               | ProvClause (_, name0) ->
                 efailure (ETypeError (body_prov,
                   (ergo_format_clause_return_error m nsctxt name0 outt
                     expectedt)))
               | _ ->
                 efailure (ETypeError (body_prov,
                   (ergo_format_function_return_error m nsctxt name outt
                     expectedt))))
       | None ->
         esuccess ({ functionct_annot = func.functionc_annot;
           functionct_sig = { sigct_params = tparams; sigct_output = outt };
           functionct_body = (Some outT) }, dctxt) []))
      (ergoc_expr_typecheck m nsctxt
        (type_context_set_local_env m.brand_model_relation dctxt tparams)
        body)
  | None ->
    let tparams =
      map (fun x -> ((fst x),
        (ergo_type_to_qcert_type m.brand_model_relation (snd x))))
        func.functionc_sig.sigc_params
    in
    let toutput =
      match func.functionc_sig.sigc_output with
      | Some eout -> ergo_type_to_qcert_type m.brand_model_relation eout
      | None -> QLib.QcertType.ttop m.brand_model_relation
    in
    esuccess ({ functionct_annot = func.functionc_annot; functionct_sig =
      { sigct_params = tparams; sigct_output = toutput }; functionct_body =
      None }, dctxt) []

(** val ergoc_clause_typecheck :
    brand_model -> namespace_ctxt -> type_context ->
    (char list * ergoc_function) ->
    ((char list * ergoct_function) * type_context) eresult **)

let ergoc_clause_typecheck m nsctxt dctxt = function
| (name, body) ->
  elift (fun fT -> ((name, (fst fT)), (snd fT)))
    (ergoc_function_typecheck m nsctxt name dctxt body)

(** val ergoc_contract_typecheck :
    brand_model -> namespace_ctxt -> type_context -> absolute_name ->
    ergoc_contract -> (ergoct_contract * type_context) eresult **)

let ergoc_contract_typecheck m nsctxt dctxt _ c =
  elift (fun cT -> ({ contractct_annot = c.contractc_annot;
    contractct_clauses = (fst cT) }, (snd cT)))
    (elift_context_fold_left (ergoc_clause_typecheck m nsctxt)
      c.contractc_clauses dctxt)

(** val ergoc_decl_typecheck :
    brand_model -> namespace_ctxt -> type_context -> ergoc_declaration ->
    (ergoct_declaration * type_context) eresult **)

let ergoc_decl_typecheck m nsctxt dctxt = function
| DCExpr (prov, expr) ->
  let exprT = ergoc_expr_typecheck m nsctxt dctxt expr in
  elift (fun xT -> ((DCTExpr ((prov, (exprct_type_annot m xT)), xT)), dctxt))
    exprT
| DCConstant (prov, name, o, expr) ->
  (match o with
   | Some t ->
     let fmt_err = fun t' vt -> ETypeError (prov,
       (append
         ('T'::('h'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('a'::('n'::('n'::('o'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('`'::[])))))))))))))))))))))
         (append (qcert_type_to_string m nsctxt t')
           (append
             ('\''::(' '::('f'::('o'::('r'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('`'::[]))))))))))))))))))))
             (append name
               (append
                 ('\''::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('i'::('t'::('s'::(' '::('a'::('c'::('t'::('u'::('a'::('l'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))))))))))))
                 (append (qcert_type_to_string m nsctxt vt) ('\''::('.'::[])))))))))
     in
     let exprT = ergoc_expr_typecheck m nsctxt dctxt expr in
     eolift (fun vT ->
       let vt = exprct_type_annot m vT in
       let t' = ergo_type_to_qcert_type m.brand_model_relation t in
       if subtype_dec enhanced_foreign_type m.brand_model_relation vt t'
       then let ctxt' =
              type_context_update_global_env m.brand_model_relation dctxt
                name t'
            in
            esuccess ((DCTConstant ((prov, t'), name, (Some t), vT)), ctxt')
              []
       else efailure (fmt_err t' vt)) exprT
   | None ->
     let exprT = ergoc_expr_typecheck m nsctxt dctxt expr in
     elift (fun xT -> ((DCTConstant ((prov, (exprct_type_annot m xT)), name,
       None, xT)),
       (type_context_update_global_env m.brand_model_relation dctxt name
         (exprct_type_annot m xT)))) exprT)
| DCFunc (prov, name, func) ->
  elift (fun fc -> ((DCTFunc (prov, name, (fst fc))), (snd fc)))
    (ergoc_function_typecheck m nsctxt name dctxt func)
| DCContract (prov, name, contr) ->
  elift (fun fc -> ((DCTContract (prov, name, (fst fc))), (snd fc)))
    (ergoc_contract_typecheck m nsctxt dctxt name contr)

(** val ergoc_module_typecheck :
    brand_model -> namespace_ctxt -> type_context -> ergoc_module ->
    (ergoct_module * type_context) eresult **)

let ergoc_module_typecheck m nsctxt dctxt mod0 =
  elift (fun x -> ({ modulect_annot = mod0.modulec_annot;
    modulect_namespace = mod0.modulec_namespace; modulect_declarations =
    (fst x) }, (snd x)))
    (elift_context_fold_left (ergoc_decl_typecheck m nsctxt)
      mod0.modulec_declarations dctxt)
