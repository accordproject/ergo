open Ast
open BinaryOperators
open Data
open Datatypes
open Ergo
open ErgoCT
open ErgoNNRC
open ErgoNNRCSugar
open ForeignRuntime
open Fresh
open List0
open Names
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators
open CNNRC

(** val ergo_pattern_to_nnrc :
    brand_model -> char list list -> ergo_nnrc_expr -> tlaergo_pattern ->
    char list list * ergo_nnrc_expr **)

let ergo_pattern_to_nnrc _ env input_expr = function
| CaseData (_, d) ->
  ([], (NNRCIf ((NNRCBinop (OpEqual, input_expr, (NNRCConst d))), (NNRCUnop
    (OpLeft, (NNRCConst (Coq_drec [])))), (NNRCUnop (OpRight, (NNRCConst
    Coq_dunit))))))
| CaseEnum (_, v) ->
  let case_d =
    if in_dec string_dec v env then NNRCGetConstant v else NNRCVar v
  in
  ([], (NNRCIf ((NNRCBinop (OpEqual, input_expr, case_d)), (NNRCUnop (OpLeft,
  (NNRCConst (Coq_drec [])))), (NNRCUnop (OpRight, (NNRCConst Coq_dunit))))))
| CaseWildcard (_, t) ->
  (match t with
   | Some type_name ->
     let (v1, v2) =
       fresh_var2 ('$'::('c'::('a'::('s'::('e'::[])))))
         ('$'::('c'::('a'::('s'::('e'::[]))))) []
     in
     ([], (NNRCEither ((NNRCUnop ((OpCast (type_name :: [])), input_expr)),
     v1, (NNRCUnop (OpLeft, (NNRCConst (Coq_drec [])))), v2, (NNRCUnop
     (OpRight, (NNRCConst Coq_dunit))))))
   | None -> ([], (NNRCUnop (OpLeft, (NNRCConst (Coq_drec []))))))
| CaseLet (_, v, t) ->
  (match t with
   | Some type_name ->
     let (v1, v2) =
       fresh_var2 ('$'::('c'::('a'::('s'::('e'::[])))))
         ('$'::('c'::('a'::('s'::('e'::[]))))) []
     in
     ((v :: []), (NNRCEither ((NNRCUnop ((OpCast (type_name :: [])),
     input_expr)), v1, (NNRCUnop (OpLeft, (NNRCUnop ((OpRec v), (NNRCVar
     v1))))), v2, (NNRCUnop (OpRight, (NNRCConst Coq_dunit))))))
   | None ->
     ((v :: []), (NNRCUnop (OpLeft, (NNRCUnop ((OpRec v), input_expr))))))
| CaseLetOption (_, v, t) ->
  (match t with
   | Some type_name ->
     let (v1, v2) =
       fresh_var2 ('$'::('c'::('a'::('s'::('e'::[])))))
         ('$'::('c'::('a'::('s'::('e'::[]))))) []
     in
     ((v :: []), (NNRCLet (v1, input_expr, (NNRCEither ((NNRCVar v1),
     ('$'::('c'::('a'::('s'::('e'::('1'::[])))))), (NNRCEither ((NNRCUnop
     ((OpCast (type_name :: [])), (NNRCVar
     ('$'::('c'::('a'::('s'::('e'::('1'::[]))))))))), v1, (NNRCUnop (OpLeft,
     (NNRCUnop ((OpRec v), (NNRCVar v1))))), v2, (NNRCUnop (OpRight,
     (NNRCConst Coq_dunit))))), ('$'::('c'::('a'::('s'::('e'::('2'::[])))))),
     (NNRCUnop (OpRight, (NNRCConst Coq_dunit))))))))
   | None ->
     let v1 = fresh_var ('$'::('c'::('a'::('s'::('e'::[]))))) [] in
     ((v :: []), (NNRCLet (v1, input_expr, (NNRCEither ((NNRCVar v1),
     ('$'::('c'::('a'::('s'::('e'::('1'::[])))))), (NNRCUnop (OpLeft,
     (NNRCUnop ((OpRec v), (NNRCVar
     ('$'::('c'::('a'::('s'::('e'::('1'::[]))))))))))),
     ('$'::('c'::('a'::('s'::('e'::('2'::[])))))), (NNRCUnop (OpRight,
     (NNRCConst Coq_dunit)))))))))

(** val pack_pattern :
    char list list -> ergo_nnrc_expr -> ergo_nnrc_expr -> ergo_nnrc_expr ->
    ergo_nnrc_expr **)

let pack_pattern vars pattern_expr else_expr cont_expr =
  let v_rec = fresh_in_case pattern_expr else_expr in
  let proc_one = fun acc v -> NNRCLet (v, (NNRCUnop ((OpDot v), (NNRCVar
    v_rec))), acc)
  in
  let inner_expr = fold_left proc_one vars else_expr in
  let (v1, v2) =
    fresh_var2 ('$'::('c'::('a'::('s'::('e'::[])))))
      ('$'::('c'::('a'::('s'::('e'::[]))))) []
  in
  NNRCEither (pattern_expr, v1, (NNRCLet (v_rec, (NNRCVar v1), inner_expr)),
  v2, cont_expr)

(** val ergoct_expr_to_nnrc :
    brand_model -> char list list -> ergoct_expr -> ergo_nnrc_expr eresult **)

let rec ergoct_expr_to_nnrc m env = function
| EThis p -> let (prov, _) = p in this_in_calculus_error prov
| EThisContract p -> let (prov, _) = p in contract_in_calculus_error prov
| EThisClause p -> let (prov, _) = p in clause_in_calculus_error prov
| EThisState p -> let (prov, _) = p in state_in_calculus_error prov
| EVar (_, v) ->
  if in_dec string_dec v env
  then esuccess (NNRCGetConstant v) []
  else esuccess (NNRCVar v) []
| EConst (_, d) -> esuccess (NNRCConst d) []
| EText (p, _) -> let (prov, _) = p in text_in_calculus_error prov
| ENone _ ->
  esuccess (NNRCConst (dnone enhanced_foreign_runtime.foreign_runtime_data))
    []
| ESome (_, e0) ->
  elift (fun x -> NNRCUnop (OpLeft, x)) (ergoct_expr_to_nnrc m env e0)
| EArray (_, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (ergoct_expr_to_nnrc m env e0) acc
  in
  elift new_array (fold_right proc_one init_el el)
| EUnaryOperator (p, _, _) ->
  let (prov, _) = p in operator_in_calculus_error prov
| EBinaryOperator (p, _, _, _) ->
  let (prov, _) = p in operator_in_calculus_error prov
| EUnaryBuiltin (_, u, e0) ->
  elift (fun x -> NNRCUnop (u, x)) (ergoct_expr_to_nnrc m env e0)
| EBinaryBuiltin (_, b, e1, e2) ->
  elift2 (fun x x0 -> NNRCBinop (b, x, x0)) (ergoct_expr_to_nnrc m env e1)
    (ergoct_expr_to_nnrc m env e2)
| EIf (_, e1, e2, e3) ->
  elift3 (fun x x0 x1 -> NNRCIf (x, x0, x1)) (ergoct_expr_to_nnrc m env e1)
    (ergoct_expr_to_nnrc m env e2) (ergoct_expr_to_nnrc m env e3)
| ELet (_, v, _, e1, e2) ->
  elift2 (fun x x0 -> NNRCLet (v, x, x0)) (ergoct_expr_to_nnrc m env e1)
    (ergoct_expr_to_nnrc m env e2)
| EPrint (p, _, _) -> let (prov, _) = p in print_in_calculus_error prov
| ERecord (_, l) ->
  (match l with
   | [] -> esuccess (NNRCConst (Coq_drec [])) []
   | p0 :: rest ->
     let (s0, init) = p0 in
     let init_rec =
       elift (fun x -> NNRCUnop ((OpRec s0), x))
         (ergoct_expr_to_nnrc m env init)
     in
     let proc_one = fun acc att ->
       let attname = fst att in
       let e0 = ergoct_expr_to_nnrc m env (snd att) in
       elift2 (fun x x0 -> NNRCBinop (OpRecConcat, x, x0)) acc
         (elift (fun x -> NNRCUnop ((OpRec attname), x)) e0)
     in
     fold_left proc_one rest init_rec)
| ENew (_, cr, l) ->
  (match l with
   | [] -> esuccess (new_expr cr (NNRCConst (Coq_drec []))) []
   | p0 :: rest ->
     let (s0, init) = p0 in
     let init_rec =
       elift (fun x -> NNRCUnop ((OpRec s0), x))
         (ergoct_expr_to_nnrc m env init)
     in
     let proc_one = fun acc att ->
       let attname = fst att in
       let e0 = ergoct_expr_to_nnrc m env (snd att) in
       elift2 (fun x x0 -> NNRCBinop (OpRecConcat, x, x0)) acc
         (elift (fun x -> NNRCUnop ((OpRec attname), x)) e0)
     in
     elift (new_expr cr) (fold_left proc_one rest init_rec))
| ECallFun (p, fname, _) ->
  let (prov, _) = p in
  function_not_inlined_error prov
    ('e'::('c'::('2'::('e'::('n'::('/'::('e'::('x'::('p'::('r'::[]))))))))))
    fname
| ECallFunInGroup (p, gname, fname, _) ->
  let (prov, _) = p in function_in_group_not_inlined_error prov gname fname
| EMatch (_, e0, ecases, edefault) ->
  let ec0 = ergoct_expr_to_nnrc m env e0 in
  let eccases =
    let proc_one = fun acc ecase ->
      eolift (fun acc0 ->
        elift (fun x -> ((fst ecase), x) :: acc0)
          (ergoct_expr_to_nnrc m env (snd ecase))) acc
    in
    fold_left proc_one ecases (esuccess [] [])
  in
  let ecdefault = ergoct_expr_to_nnrc m env edefault in
  eolift (fun ec1 ->
    eolift (fun eccases0 ->
      eolift (fun ecdefault0 ->
        let v0 = fresh_in_match eccases0 ecdefault0 in
        let proc_one_case = fun acc ecase ->
          let (vars, pattern_expr) =
            ergo_pattern_to_nnrc m env (NNRCVar v0) (fst ecase)
          in
          elift (fun cont_expr ->
            pack_pattern vars pattern_expr (snd ecase) cont_expr) acc
        in
        let eccases_folded =
          fold_left proc_one_case eccases0 (esuccess ecdefault0 [])
        in
        elift (fun x -> NNRCLet (v0, ec1, x)) eccases_folded) ecdefault)
      eccases) ec0
| EForeach (loc, l, o, e2) ->
  let (prov, _) = loc in
  (match l with
   | [] -> complex_foreach_in_calculus_error prov
   | p :: l0 ->
     let (v, e1) = p in
     (match l0 with
      | [] ->
        (match o with
         | Some _ -> complex_foreach_in_calculus_error prov
         | None ->
           elift2 (fun x x0 -> NNRCFor (v, x, x0))
             (ergoct_expr_to_nnrc m env e1) (ergoct_expr_to_nnrc m env e2))
      | _ :: _ -> complex_foreach_in_calculus_error prov))
| EAs (p, _, _) -> let (prov, _) = p in as_in_calculus_error prov

(** val functionct_to_nnrc :
    brand_model -> absolute_name -> ergoct_function ->
    (char list * ergo_nnrc_lambda) eresult **)

let functionct_to_nnrc m fn f =
  let env =
    current_time :: (options :: (map fst f.functionct_sig.sigct_params))
  in
  (match f.functionct_body with
   | Some body ->
     elift (fun x -> (fn, x))
       (elift (fun x -> { lambdan_provenance = f.functionct_annot;
         lambdan_params = f.functionct_sig.sigct_params; lambdan_output =
         f.functionct_sig.sigct_output; lambdan_body = x })
         (ergoct_expr_to_nnrc m env body))
   | None ->
     function_not_inlined_error f.functionct_annot
       ('e'::('c'::('2'::('e'::('n'::('/'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))
       fn)

(** val clausect_declaration_to_nnrc :
    brand_model -> absolute_name -> ergoct_function ->
    (char list * ergo_nnrc_lambda) eresult **)

let clausect_declaration_to_nnrc =
  functionct_to_nnrc

(** val contractct_to_nnrc :
    brand_model -> ergoct_contract -> ergo_nnrc_function_table eresult **)

let contractct_to_nnrc m c =
  let init = esuccess [] [] in
  let proc_one = fun acc s ->
    eolift (fun acc0 ->
      elift (fun news -> news :: acc0)
        (clausect_declaration_to_nnrc m (fst s) (snd s))) acc
  in
  elift (fun x -> { function_tablen_provenance = c.contractct_annot;
    function_tablen_funs = x }) (fold_left proc_one c.contractct_clauses init)

(** val declarationct_to_nnrc :
    brand_model -> ergoct_declaration -> ergo_nnrc_declaration list eresult **)

let declarationct_to_nnrc m = function
| DCTFunc (_, fn, f) ->
  elift (fun f0 -> (DNFunc ((fst f0), (snd f0))) :: [])
    (functionct_to_nnrc m fn f)
| DCTContract (_, cn, c) ->
  elift (fun f -> (DNFuncTable (cn, f)) :: []) (contractct_to_nnrc m c)
| _ -> esuccess [] []

(** val declarationsct_calculus_with_table :
    brand_model -> ergoct_declaration list -> ergo_nnrc_declaration list
    eresult **)

let declarationsct_calculus_with_table m dl =
  let init = esuccess [] [] in
  let proc_one = fun acc s ->
    eolift (fun acc0 ->
      let edecl = declarationct_to_nnrc m s in
      elift (fun news -> app news acc0) edecl) acc
  in
  fold_left proc_one dl init

(** val modulect_to_nnrc_with_table :
    brand_model -> ergoct_module -> ergo_nnrc_module eresult **)

let modulect_to_nnrc_with_table m p =
  elift (fun x -> { modulen_provenance = p.modulect_annot;
    modulen_namespace = p.modulect_namespace; modulen_declarations = x })
    (declarationsct_calculus_with_table m p.modulect_declarations)

(** val ergoct_module_to_nnrc :
    brand_model -> ergoct_module -> ergo_nnrc_module eresult **)

let ergoct_module_to_nnrc =
  modulect_to_nnrc_with_table
