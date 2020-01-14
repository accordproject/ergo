open BinaryOperators
open Data
open Datatypes
open Ergo
open ErgoC
open ErgoCSugar
open ErgoCompContext
open ErgoType
open List0
open Names
open Provenance
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators

(** val ergo_expr_to_ergoc_expr :
    brand_model -> compilation_context -> laergo_expr -> ergoc_expr eresult **)

let rec ergo_expr_to_ergoc_expr bm ctxt = function
| EThis prov ->
  (match ctxt.compilation_context_current_contract with
   | Some _ -> esuccess (thisThis prov) []
   | None -> use_contract_not_in_contract_error prov)
| EThisContract prov ->
  (match ctxt.compilation_context_current_contract with
   | Some _ -> esuccess (thisContract prov) []
   | None -> use_contract_not_in_contract_error prov)
| EThisClause prov ->
  (match ctxt.compilation_context_current_clause with
   | Some clause_name0 -> esuccess (thisClause prov clause_name0) []
   | None -> not_in_clause_error prov)
| EThisState prov -> esuccess (thisState prov) []
| EText (prov, el) ->
  let init_el = esuccess (EConst (prov, (Coq_dstring []))) [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> EBinaryBuiltin (prov, OpStringConcat, x, x0))
      (ergo_expr_to_ergoc_expr bm ctxt e0) acc
  in
  fold_right proc_one init_el el
| ESome (prov, e0) ->
  elift (fun x -> ESome (prov, x)) (ergo_expr_to_ergoc_expr bm ctxt e0)
| EArray (prov, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (ergo_expr_to_ergoc_expr bm ctxt e0) acc
  in
  elift (fun x -> EArray (prov, x)) (fold_right proc_one init_el el)
| EUnaryOperator (prov, u, e0) ->
  elift (fun x -> EUnaryOperator (prov, u, x))
    (ergo_expr_to_ergoc_expr bm ctxt e0)
| EBinaryOperator (prov, b, e1, e2) ->
  elift2 (fun x x0 -> EBinaryOperator (prov, b, x, x0))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_expr_to_ergoc_expr bm ctxt e2)
| EUnaryBuiltin (prov, u, e0) ->
  elift (fun x -> EUnaryBuiltin (prov, u, x))
    (ergo_expr_to_ergoc_expr bm ctxt e0)
| EBinaryBuiltin (prov, b, e1, e2) ->
  elift2 (fun x x0 -> EBinaryBuiltin (prov, b, x, x0))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_expr_to_ergoc_expr bm ctxt e2)
| EIf (prov, e1, e2, e3) ->
  elift3 (fun x x0 x1 -> EIf (prov, x, x0, x1))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_expr_to_ergoc_expr bm ctxt e2)
    (ergo_expr_to_ergoc_expr bm ctxt e3)
| ELet (prov, v, ta, e1, e2) ->
  elift2 (fun x x0 -> ELet (prov, v, ta, x, x0))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_expr_to_ergoc_expr bm ctxt e2)
| EPrint (prov, e1, e2) ->
  elift2 (fun x x0 -> ELet (prov,
    ('_'::('_'::('l'::('o'::('g'::('_'::('_'::[]))))))), None, x, x0))
    (elift (fun x -> EUnaryBuiltin (prov, (OpForeignUnary
      (Obj.magic Coq_enhanced_unary_log_op)), x))
      (elift (fun x -> EUnaryBuiltin (prov, OpToString, x))
        (ergo_expr_to_ergoc_expr bm ctxt e1)))
    (ergo_expr_to_ergoc_expr bm ctxt e2)
| ERecord (prov, el) ->
  let init_rec = esuccess [] [] in
  let proc_one = fun att acc ->
    let attname = fst att in
    let e0 = ergo_expr_to_ergoc_expr bm ctxt (snd att) in
    elift2 (fun e1 acc0 -> (attname, e1) :: acc0) e0 acc
  in
  elift (fun x -> ERecord (prov, x)) (fold_right proc_one init_rec el)
| ENew (prov, cr, el) ->
  if is_abstract_class bm ctxt cr
  then efailure (ECompilationError (prov,
         (append
           ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('r'::('e'::('a'::('t'::('e'::(' '::('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::(' '::('o'::('f'::(' '::('a'::('b'::('s'::('t'::('r'::('a'::('c'::('t'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))
           (append cr ('\''::[])))))
  else let init_rec = esuccess [] [] in
       let proc_one = fun att acc ->
         let attname = fst att in
         let e0 = ergo_expr_to_ergoc_expr bm ctxt (snd att) in
         elift2 (fun e1 acc0 -> (attname, e1) :: acc0) e0 acc
       in
       elift (fun x -> ENew (prov, cr, x)) (fold_right proc_one init_rec el)
| ECallFun (prov, fname, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (ergo_expr_to_ergoc_expr bm ctxt e0) acc
  in
  elift (fun x -> ECallFun (prov, fname, x)) (fold_right proc_one init_el el)
| ECallFunInGroup (prov, gname, fname, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (ergo_expr_to_ergoc_expr bm ctxt e0) acc
  in
  elift (fun x -> ECallFunInGroup (prov, gname, fname, x))
    (fold_right proc_one init_el el)
| EMatch (prov, e0, ecases, edefault) ->
  let ec0 = ergo_expr_to_ergoc_expr bm ctxt e0 in
  let eccases =
    let proc_one = fun acc ecase ->
      eolift (fun acc0 ->
        elift (fun x -> ((fst ecase), x) :: acc0)
          (ergo_expr_to_ergoc_expr bm ctxt (snd ecase))) acc
    in
    fold_left proc_one ecases (esuccess [] [])
  in
  let ecdefault = ergo_expr_to_ergoc_expr bm ctxt edefault in
  eolift (fun ec1 ->
    eolift (fun eccases0 ->
      elift (fun ecdefault0 -> EMatch (prov, ec1, eccases0, ecdefault0))
        ecdefault) eccases) ec0
| EForeach (prov, foreachs, econd, e2) ->
  let init_e2 =
    elift (fun x -> EUnaryBuiltin (prov, OpBag, x))
      (ergo_expr_to_ergoc_expr bm ctxt e2)
  in
  let init_e =
    match econd with
    | Some econd0 ->
      elift2 (fun econd1 e3 -> EIf (prov, econd1, e3, (EConst (prov,
        (Coq_dcoll []))))) (ergo_expr_to_ergoc_expr bm ctxt econd0) init_e2
    | None -> init_e2
  in
  let proc_one = fun foreach acc ->
    let v = fst foreach in
    let e0 = ergo_expr_to_ergoc_expr bm ctxt (snd foreach) in
    elift (fun x -> EUnaryBuiltin (prov, OpFlatten, x))
      (eolift (fun single ->
        elift (fun x -> EForeach (prov, ((v, single) :: []), None, x)) acc)
        e0)
  in
  fold_right proc_one init_e foreachs
| EAs (prov, f, e0) ->
  elift (fun x -> EAs (prov, f, x)) (ergo_expr_to_ergoc_expr bm ctxt e0)
| x -> esuccess x []

(** val ergo_stmt_to_expr :
    brand_model -> compilation_context -> laergo_stmt -> ergoc_expr eresult **)

let rec ergo_stmt_to_expr bm ctxt = function
| SReturn (prov, e) ->
  elift (coq_EReturn prov) (ergo_expr_to_ergoc_expr bm ctxt e)
| SFunReturn (_, e) -> ergo_expr_to_ergoc_expr bm ctxt e
| SThrow (prov, e) ->
  elift (coq_EFailure prov) (ergo_expr_to_ergoc_expr bm ctxt e)
| SCallClause (prov, e0, clname, el) ->
  (match e0 with
   | EThisContract _ ->
     (match ctxt.compilation_context_current_contract with
      | Some coname ->
        let el0 = emaplift (ergo_expr_to_ergoc_expr bm ctxt) el in
        elift (coq_ECallClause prov coname clname) el0
      | None -> call_clause_not_in_contract_error prov clname)
   | _ -> clause_call_not_on_contract_error (expr_annot e0))
| SCallContract (prov, e0, el) ->
  (match e0 with
   | EThisContract _ ->
     (match ctxt.compilation_context_current_contract with
      | Some coname ->
        let el0 = emaplift (ergo_expr_to_ergoc_expr bm ctxt) el in
        elift (coq_ECallClause prov coname clause_main_name) el0
      | None -> call_clause_not_in_contract_error prov clause_main_name)
   | _ -> clause_call_not_on_contract_error (expr_annot e0))
| SSetState (prov, e1, s2) ->
  elift2 (setState prov) (ergo_expr_to_ergoc_expr bm ctxt e1)
    (ergo_stmt_to_expr bm ctxt s2)
| SSetStateDot (prov, a, e1, s2) ->
  (match is_state_type_branded bm ctxt with
   | Some tname ->
     elift2 (setStateDot prov a tname) (ergo_expr_to_ergoc_expr bm ctxt e1)
       (ergo_stmt_to_expr bm ctxt s2)
   | None -> set_state_on_non_brand_error (expr_annot e1) a)
| SEmit (prov, e1, s2) ->
  elift2 (pushEmit prov) (ergo_expr_to_ergoc_expr bm ctxt e1)
    (ergo_stmt_to_expr bm ctxt s2)
| SLet (prov, vname, vtype, e1, s2) ->
  elift2 (fun x x0 -> ELet (prov, vname, vtype, x, x0))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_stmt_to_expr bm ctxt s2)
| SPrint (prov, e1, s2) ->
  elift2 (fun x x0 -> ELet (prov,
    ('_'::('_'::('l'::('o'::('g'::('_'::('_'::[]))))))), None, x, x0))
    (elift (fun x -> EUnaryBuiltin (prov, (OpForeignUnary
      (Obj.magic Coq_enhanced_unary_log_op)), x))
      (elift (fun x -> EUnaryBuiltin (prov, OpToString, x))
        (ergo_expr_to_ergoc_expr bm ctxt e1))) (ergo_stmt_to_expr bm ctxt s2)
| SIf (prov, e1, s2, s3) ->
  elift3 (fun x x0 x1 -> EIf (prov, x, x0, x1))
    (ergo_expr_to_ergoc_expr bm ctxt e1) (ergo_stmt_to_expr bm ctxt s2)
    (ergo_stmt_to_expr bm ctxt s3)
| SEnforce (prov, e1, o, s3) ->
  (match o with
   | Some s2 ->
     elift3 (fun x x0 x1 -> EIf (prov, x, x0, x1))
       (elift (fun x -> EUnaryBuiltin (prov, OpNeg, x))
         (ergo_expr_to_ergoc_expr bm ctxt e1)) (ergo_stmt_to_expr bm ctxt s2)
       (ergo_stmt_to_expr bm ctxt s3)
   | None ->
     elift3 (fun x x0 x1 -> EIf (prov, x, x0, x1))
       (elift (fun x -> EUnaryBuiltin (prov, OpNeg, x))
         (ergo_expr_to_ergoc_expr bm ctxt e1))
       (esuccess
         (coq_EFailure prov (EConst (prov, (enforce_error_content prov []))))
         ((warning_no_else prov) :: [])) (ergo_stmt_to_expr bm ctxt s3))
| SMatch (prov, e0, scases, sdefault) ->
  let ec0 = ergo_expr_to_ergoc_expr bm ctxt e0 in
  let sccases =
    let proc_one = fun acc scase ->
      eolift (fun acc0 ->
        elift (fun x -> ((fst scase), x) :: acc0)
          (ergo_stmt_to_expr bm ctxt (snd scase))) acc
    in
    fold_left proc_one scases (esuccess [] [])
  in
  let scdefault = ergo_stmt_to_expr bm ctxt sdefault in
  eolift (fun ec1 ->
    eolift (fun sccases0 ->
      elift (fun scdefault0 -> EMatch (prov, ec1, sccases0, scdefault0))
        scdefault) sccases) ec0

(** val clause_to_calculus :
    brand_model -> compilation_context -> laergo_type -> laergo_type option
    -> laergo_clause -> (local_name * ergoc_function) eresult **)

let clause_to_calculus bm ctxt template state c =
  let ctxt0 = set_current_clause bm ctxt c.clause_name in
  let prov = ProvClause ((loc_of_provenance c.clause_annot), c.clause_name) in
  let clname = c.clause_name in
  let emit = c.clause_sig.type_signature_emits in
  let response = c.clause_sig.type_signature_output in
  let body =
    match c.clause_body with
    | Some stmt -> elift (fun x -> Some x) (ergo_stmt_to_expr bm ctxt0 stmt)
    | None -> esuccess None []
  in
  let params = c.clause_sig.type_signature_params in
  elift
    (coq_EClauseAsFunction prov clname template emit state response params)
    body

(** val function_to_calculus :
    brand_model -> compilation_context -> laergo_function -> ergoc_function
    eresult **)

let function_to_calculus bm ctxt f =
  let body =
    match f.function_body with
    | Some e -> elift (fun x -> Some x) (ergo_expr_to_ergoc_expr bm ctxt e)
    | None -> esuccess None []
  in
  elift (fun x -> { functionc_annot = f.function_annot; functionc_sig =
    { sigc_params = f.function_sig.type_signature_params; sigc_output =
    f.function_sig.type_signature_output }; functionc_body = x }) body

(** val contract_to_calculus :
    brand_model -> compilation_context -> laergo_contract -> ergoc_contract
    eresult **)

let contract_to_calculus bm ctxt c =
  let clauses =
    emaplift
      (clause_to_calculus bm ctxt c.contract_template c.contract_state)
      c.contract_clauses
  in
  elift (fun x -> { contractc_annot = c.contract_annot; contractc_template =
    c.contract_template; contractc_state = c.contract_state;
    contractc_clauses = x }) clauses

(** val ergo_stmt_to_expr_top :
    brand_model -> compilation_context -> provenance -> (provenance,
    provenance, absolute_name) ergo_stmt -> ergoc_expr eresult **)

let ergo_stmt_to_expr_top bm ctxt prov s =
  elift (coq_EWrapTop prov) (ergo_stmt_to_expr bm ctxt s)

(** val declaration_to_calculus :
    brand_model -> compilation_context -> laergo_declaration ->
    (ergoc_declaration list * compilation_context) eresult **)

let declaration_to_calculus bm ctxt = function
| DType (prov, ergo_type) ->
  let name = ergo_type.type_declaration_name in
  if in_dec string_dec name
       (map (fun e -> e.type_declaration_name)
         ctxt.compilation_context_new_type_decls)
  then efailure (ECompilationError (prov,
         (append
           ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('r'::('e'::('d'::('e'::('f'::('i'::('n'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))
           (append name ('\''::[])))))
  else esuccess ([],
         (compilation_context_add_new_type_declaration bm ctxt ergo_type)) []
| DStmt (prov, s) ->
  elift (fun x -> ((x :: []), ctxt))
    (elift (fun x -> DCExpr (prov, x)) (ergo_stmt_to_expr_top bm ctxt prov s))
| DConstant (prov, v, ta, e) ->
  elift (fun x -> ((x :: []), ctxt))
    (elift (fun x -> DCConstant (prov, v, ta, x))
      (ergo_expr_to_ergoc_expr bm ctxt e))
| DFunc (prov, fn, f) ->
  elift (fun x -> ((x :: []), ctxt))
    (elift (fun x -> DCFunc (prov, fn, x)) (function_to_calculus bm ctxt f))
| DContract (prov, cn, c) ->
  elift (fun x -> ((x :: []), ctxt))
    (elift (fun x -> DCContract (prov, cn, x))
      (let statet = c.contract_state in
       let ctxt0 = set_current_contract bm ctxt cn statet in
       contract_to_calculus bm ctxt0 c))
| DSetContract (prov, cn, e1) ->
  let ctxt0 = set_current_contract bm ctxt cn None in
  elift (fun x -> (((DCConstant (prov, this_contract, None,
    x)) :: ((DCConstant (prov, local_state, None, (EConst (prov,
    Coq_dunit)))) :: [])), ctxt0)) (ergo_expr_to_ergoc_expr bm ctxt0 e1)
| _ -> esuccess ([], ctxt) []

(** val declarations_calculus :
    brand_model -> compilation_context -> (provenance, provenance,
    absolute_name) ergo_declaration list -> (ergoc_declaration
    list * compilation_context) eresult **)

let declarations_calculus bm ctxt dl =
  let proc_one = fun acc d ->
    eolift (fun acc0 ->
      let (acc1, ctxt0) = acc0 in
      elift (fun decls ->
        let (decls0, ctxt1) = decls in ((app acc1 decls0), ctxt1))
        (declaration_to_calculus bm ctxt0 d)) acc
  in
  fold_left proc_one dl (esuccess ([], ctxt) [])

(** val ergo_module_to_calculus :
    brand_model -> compilation_context -> laergo_module ->
    (ergoc_module * compilation_context) eresult **)

let ergo_module_to_calculus bm ctxt p =
  elift (fun res ->
    let (decls, ctxt0) = res in
    ({ modulec_annot = p.module_annot; modulec_namespace =
    p.module_namespace; modulec_declarations = decls }, ctxt0))
    (declarations_calculus bm ctxt p.module_declarations)
