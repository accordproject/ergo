open Assoc
open Ast
open BinaryOperators
open Bindings
open BrandRelation
open Data
open Datatypes
open Ergo
open ErgoCEvalContext
open ErgoCT
open List0
open Provenance
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators

(** val ergo_unary_builtin_eval :
    brand_model -> provenance -> unary_op -> QLib.qcert_data ->
    QLib.qcert_data eresult **)

let ergo_unary_builtin_eval m prov o d =
  match QLib.QcertOps.Unary.eval
          (brand_relation_brands m.brand_model_relation) o d with
  | Some r -> esuccess r []
  | None -> eval_unary_builtin_error prov o

(** val ergo_binary_builtin_eval :
    brand_model -> provenance -> binary_op -> QLib.qcert_data ->
    QLib.qcert_data -> QLib.qcert_data eresult **)

let ergo_binary_builtin_eval m prov o d1 d2 =
  match QLib.QcertOps.Binary.eval
          (brand_relation_brands m.brand_model_relation) o d1 d2 with
  | Some r -> esuccess r []
  | None -> eval_binary_builtin_error prov o

(** val ergoct_eval_expr :
    brand_model -> eval_context -> ergoct_expr -> QLib.qcert_data eresult **)

let rec ergoct_eval_expr m ctxt = function
| EThis p -> let (prov, _) = p in this_in_calculus_error prov
| EThisContract p -> let (prov, _) = p in contract_in_calculus_error prov
| EThisClause p -> let (prov, _) = p in clause_in_calculus_error prov
| EThisState p -> let (prov, _) = p in state_in_calculus_error prov
| EVar (p, name) ->
  let (prov, _) = p in
  (match lookup string_dec
           (app ctxt.eval_context_local_env ctxt.eval_context_global_env) name with
   | Some d -> esuccess d []
   | None -> variable_name_not_found_error prov name)
| EConst (_, d) -> esuccess d []
| EText (p, _) -> let (prov, _) = p in text_in_calculus_error prov
| ENone _ -> esuccess (dnone enhanced_foreign_data) []
| ESome (_, e) ->
  elift (dsome enhanced_foreign_data) (ergoct_eval_expr m ctxt e)
| EArray (_, es) ->
  let rcoll = emaplift (ergoct_eval_expr m ctxt) es in
  elift (fun x -> Coq_dcoll x) rcoll
| EUnaryOperator (p, o, _) ->
  let (prov, _) = p in eval_unary_operator_error prov o
| EBinaryOperator (p, o, _, _) ->
  let (prov, _) = p in eval_binary_operator_error prov o
| EUnaryBuiltin (p, o, e) ->
  let (prov, _) = p in
  eolift (ergo_unary_builtin_eval m prov o) (ergoct_eval_expr m ctxt e)
| EBinaryBuiltin (p, o, e1, e2) ->
  let (prov, _) = p in
  eolift2 (ergo_binary_builtin_eval m prov o) (ergoct_eval_expr m ctxt e1)
    (ergoct_eval_expr m ctxt e2)
| EIf (p, c, t, f) ->
  let (prov, _) = p in
  eolift (fun d ->
    match d with
    | Coq_dbool b ->
      if b then ergoct_eval_expr m ctxt t else ergoct_eval_expr m ctxt f
    | _ -> eval_if_not_boolean_error prov) (ergoct_eval_expr m ctxt c)
| ELet (_, n, _, e1, e2) ->
  eolift (fun d ->
    let ctxt' = eval_context_update_local_env ctxt n d in
    ergoct_eval_expr m ctxt' e2) (ergoct_eval_expr m ctxt e1)
| EPrint (p, _, _) -> let (prov, _) = p in print_in_calculus_error prov
| ERecord (_, rs) ->
  let rrec =
    emaplift (fun nv ->
      let att = fst nv in
      let e = snd nv in elift (fun d -> (att, d)) (ergoct_eval_expr m ctxt e))
      rs
  in
  elift (fun x -> Coq_drec x) (elift (rec_sort coq_ODT_string) rrec)
| ENew (_, nr, rs) ->
  let rrec =
    emaplift (fun nv ->
      let att = fst nv in
      let e = snd nv in elift (fun d -> (att, d)) (ergoct_eval_expr m ctxt e))
      rs
  in
  elift (fun r -> Coq_dbrand ((nr :: []), (Coq_drec
    (rec_sort coq_ODT_string r)))) rrec
| ECallFun (p, fname, _) ->
  let (prov, _) = p in
  function_not_inlined_error prov ('e'::('v'::('a'::('l'::[])))) fname
| ECallFunInGroup (p, gname, fname, _) ->
  let (prov, _) = p in function_in_group_not_inlined_error prov gname fname
| EMatch (_, term, pes, default) ->
  let lift_dbrand = fun dat brand fn default0 ->
    match dat with
    | Coq_dbrand (b, _) ->
      (match b with
       | [] -> default0
       | br :: l ->
         (match l with
          | [] ->
            if sub_brands_dec (brand_relation_brands m.brand_model_relation)
                 (br :: []) (brand :: [])
            then fn dat
            else default0
          | _ :: _ -> default0))
    | _ -> default0
  in
  let apply_match = fun dat ->
    fold_right (fun pe default_result ->
      let (t, res) = pe in
      (match t with
       | CaseData (_, d) ->
         if data_eq_dec enhanced_foreign_data d dat
         then ergoct_eval_expr m ctxt res
         else default_result
       | CaseEnum (p, name) ->
         let (prov, _) = p in
         let case_d =
           match lookup string_dec
                   (app ctxt.eval_context_local_env
                     ctxt.eval_context_global_env) name with
           | Some d -> esuccess d []
           | None -> enum_name_not_found_error prov name
         in
         eolift (fun d ->
           if data_eq_dec enhanced_foreign_data d dat
           then ergoct_eval_expr m ctxt res
           else default_result) case_d
       | CaseWildcard (_, t0) ->
         (match t0 with
          | Some typ ->
            lift_dbrand dat typ (fun _ -> ergoct_eval_expr m ctxt res)
              default_result
          | None -> ergoct_eval_expr m ctxt res)
       | CaseLet (_, name, t0) ->
         (match t0 with
          | Some typ ->
            lift_dbrand dat typ (fun dat' ->
              ergoct_eval_expr m
                (eval_context_update_local_env ctxt name dat') res)
              default_result
          | None ->
            ergoct_eval_expr m (eval_context_update_local_env ctxt name dat)
              res)
       | CaseLetOption (_, name, t0) ->
         (match t0 with
          | Some typ ->
            (match dat with
             | Coq_dleft dat' ->
               lift_dbrand dat' typ (fun dat'0 ->
                 ergoct_eval_expr m
                   (eval_context_update_local_env ctxt name dat'0) res)
                 default_result
             | _ -> default_result)
          | None ->
            (match dat with
             | Coq_dleft dat' ->
               ergoct_eval_expr m
                 (eval_context_update_local_env ctxt name dat') res
             | _ -> default_result)))) (ergoct_eval_expr m ctxt default) pes
  in
  eolift apply_match (ergoct_eval_expr m ctxt term)
| EForeach (p, l, o, fn) ->
  let (prov, _) = p in
  (match l with
   | [] -> complex_foreach_in_calculus_error prov
   | p0 :: l0 ->
     let (name, arr) = p0 in
     (match l0 with
      | [] ->
        (match o with
         | Some _ -> complex_foreach_in_calculus_error prov
         | None ->
           let rcoll =
             eolift (fun d ->
               match d with
               | Coq_dcoll arr' ->
                 emaplift (fun elt ->
                   ergoct_eval_expr m
                     (eval_context_update_local_env ctxt name elt) fn) arr'
               | _ -> eval_foreach_not_on_array_error prov)
               (ergoct_eval_expr m ctxt arr)
           in
           elift (fun x -> Coq_dcoll x) rcoll)
      | _ :: _ -> complex_foreach_in_calculus_error prov))
| EAs (p, _, _) -> let (prov, _) = p in as_in_calculus_error prov

(** val ergoct_eval_decl :
    brand_model -> eval_context -> ergoct_declaration ->
    (eval_context * QLib.qcert_data option) eresult **)

let ergoct_eval_decl m dctxt = function
| DCTExpr (_, expr) ->
  elift (fun x -> (dctxt, (Some x))) (ergoct_eval_expr m dctxt expr)
| DCTConstant (_, name, _, expr) ->
  let expr' = ergoct_eval_expr m dctxt expr in
  eolift (fun val0 ->
    esuccess ((eval_context_update_global_env dctxt name val0), None) [])
    expr'
| _ -> esuccess (dctxt, None) []
