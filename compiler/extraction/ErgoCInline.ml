open Assoc
open Datatypes
open Ergo
open ErgoC
open ErgoCStdlib
open ErgoCSugar
open ErgoCompContext
open ErgoMap
open ErgoType
open List0
open Names
open Provenance
open QLib
open Result0
open String0
open TBrandModel
open UnaryOperators

type ergo_expr = laergo_expr

(** val ergo_map_expr_sane :
    brand_model -> compilation_context -> (compilation_context ->
    (provenance, provenance, absolute_name) Ergo.ergo_expr -> (provenance,
    provenance, absolute_name) Ergo.ergo_expr eresult option) -> (provenance,
    provenance, absolute_name) Ergo.ergo_expr -> (provenance, provenance,
    absolute_name) Ergo.ergo_expr eresult **)

let ergo_map_expr_sane bm ctxt fn expr =
  ergo_map_expr (fun ctxt0 name expr0 ->
    compilation_context_update_local_env bm ctxt0 name expr0) fn ctxt expr

(** val ergo_letify_function' :
    provenance -> ergo_expr -> ((char list * laergo_type option) * ergo_expr)
    list -> ergo_expr **)

let rec ergo_letify_function' prov body = function
| [] -> body
| p :: rest ->
  let (p0, v) = p in
  let (n, t) = p0 in
  ELet (prov, n, t, v, (ergo_letify_function' prov body rest))

(** val keep_param_types :
    (char list * laergo_type) list -> (char list * laergo_type option) list **)

let keep_param_types params =
  map (fun xy -> ((fst xy), (Some (snd xy)))) params

(** val discard_param_types :
    (char list * laergo_type) list -> (char list * laergo_type option) list **)

let discard_param_types params =
  map (fun xy -> ((fst xy), None)) params

(** val ergo_letify_function :
    provenance -> char list -> ergoc_function -> ergo_expr list -> ergo_expr
    eresult **)

let ergo_letify_function prov fname fn args =
  let fndesc =
    match fn.functionc_body with
    | Some _ ->
      esuccess (fn.functionc_body,
        (keep_param_types fn.functionc_sig.sigc_params)) []
    | None ->
      (match lookup string_dec ergoc_stdlib fname with
       | Some fn0 ->
         let fn1 = fn0 prov in
         esuccess (fn1.functionc_body,
           (discard_param_types fn1.functionc_sig.sigc_params)) []
       | None -> built_in_function_not_found_error prov fname)
  in
  eolift (fun fndesc0 ->
    let (fnbody, fnparams) = fndesc0 in
    (match fnbody with
     | Some body ->
       (match zip fnparams args with
        | Some args' ->
          esuccess
            (ergo_letify_function' (ProvFunc ((loc_of_provenance prov),
              fname)) body args') []
        | None -> call_params_error prov fname)
     | None -> built_in_function_without_body_error prov fname)) fndesc

(** val ergo_inline_functions' :
    brand_model -> compilation_context -> ergo_expr -> ergo_expr eresult
    option **)

let ergo_inline_functions' _ ctxt = function
| ECallFun (prov, fname, args) ->
  Some
    (match lookup string_dec ctxt.compilation_context_function_env fname with
     | Some fn -> ergo_letify_function prov fname fn args
     | None -> function_not_found_error prov fname)
| ECallFunInGroup (prov, gname, fname, args) ->
  Some
    (match lookup string_dec ctxt.compilation_context_function_group_env gname with
     | Some t ->
       (match lookup string_dec t fname with
        | Some fn -> ergo_letify_function prov fname fn args
        | None -> function_not_found_error prov fname)
     | None -> function_not_found_error prov fname)
| _ -> None

(** val ergo_inline_functions :
    brand_model -> compilation_context -> (provenance, provenance,
    absolute_name) Ergo.ergo_expr -> (provenance, provenance, absolute_name)
    Ergo.ergo_expr eresult **)

let ergo_inline_functions bm ctxt =
  ergo_map_expr_sane bm ctxt (ergo_inline_functions' bm)

(** val ergo_inline_globals' :
    brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult
    option **)

let ergo_inline_globals' _ ctxt expr = match expr with
| EVar (prov, name) ->
  (match lookup string_dec ctxt.compilation_context_local_env name with
   | Some _ -> Some (esuccess expr [])
   | None ->
     if in_dec string_dec name ctxt.compilation_context_params_env
     then Some (esuccess expr [])
     else (match lookup string_dec ctxt.compilation_context_global_env name with
           | Some val0 -> Some (esuccess val0 [])
           | None ->
             (match lookup string_dec ctxt.compilation_context_local_env
                      this_this with
              | Some _ ->
                Some
                  (esuccess (EUnaryBuiltin (prov, (OpDot name),
                    (EUnaryBuiltin (prov, OpUnbrand, (thisThis prov))))) [])
              | None -> Some (esuccess expr []))))
| _ -> None

(** val ergo_inline_globals :
    brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult **)

let ergo_inline_globals bm ctxt expr =
  ergo_map_expr_sane bm ctxt (ergo_inline_globals' bm) expr

(** val ergo_inline_expr :
    brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult **)

let ergo_inline_expr bm ctxt expr =
  eolift (ergo_inline_functions bm ctxt) (ergo_inline_globals bm ctxt expr)

(** val ergo_inline_function :
    brand_model -> compilation_context -> ergoc_function -> ergoc_function
    eresult **)

let ergo_inline_function bm ctxt fn =
  let params = map fst fn.functionc_sig.sigc_params in
  let ctxt0 = compilation_context_set_params_env bm ctxt params in
  (match fn.functionc_body with
   | Some expr ->
     elift (fun new_body -> { functionc_annot = fn.functionc_annot;
       functionc_sig = fn.functionc_sig; functionc_body = (Some new_body) })
       (ergo_inline_expr bm ctxt0 expr)
   | None -> esuccess fn [])

(** val ergoc_inline_clause :
    brand_model -> char list -> compilation_context ->
    (char list * ergoc_function) ->
    ((char list * ergoc_function) * compilation_context) eresult **)

let ergoc_inline_clause bm coname ctxt = function
| (clname, fn) ->
  elift (fun x -> ((clname, x),
    (compilation_context_update_function_group_env bm ctxt coname clname x)))
    (ergo_inline_function bm ctxt fn)

(** val ergo_inline_contract :
    brand_model -> char list -> compilation_context -> ergoc_contract ->
    (ergoc_contract * compilation_context) eresult **)

let ergo_inline_contract bm coname ctxt contract =
  let clauses =
    elift_context_fold_left (ergoc_inline_clause bm coname)
      contract.contractc_clauses ctxt
  in
  elift (fun xy -> ({ contractc_annot = contract.contractc_annot;
    contractc_template = contract.contractc_template; contractc_state =
    contract.contractc_state; contractc_clauses = (fst xy) }, (snd xy)))
    clauses

(** val ergoc_inline_declaration :
    brand_model -> compilation_context -> ergoc_declaration ->
    (ergoc_declaration * compilation_context) eresult **)

let ergoc_inline_declaration bm ctxt = function
| DCExpr (prov, expr) ->
  elift (fun x -> ((DCExpr (prov, x)), ctxt)) (ergo_inline_expr bm ctxt expr)
| DCConstant (prov, name, ta, expr) ->
  let global_shadowing_warning =
    match lookup string_dec ctxt.compilation_context_global_env name with
    | Some _ -> (warning_global_shadowing prov name) :: []
    | None -> []
  in
  eolift (fun x ->
    esuccess ((DCConstant (prov, name, ta, x)),
      (compilation_context_update_global_env bm ctxt name x))
      global_shadowing_warning) (ergo_inline_expr bm ctxt expr)
| DCFunc (prov, name, fn) ->
  elift (fun x -> ((DCFunc (prov, name, x)),
    (compilation_context_update_function_env bm ctxt name x)))
    (ergo_inline_function bm ctxt fn)
| DCContract (prov, name, c) ->
  elift (fun xy -> ((DCContract (prov, name, (fst xy))), (snd xy)))
    (ergo_inline_contract bm name ctxt c)

(** val ergoc_inline_declarations :
    brand_model -> compilation_context -> ergoc_declaration list ->
    (ergoc_declaration list * compilation_context) eresult **)

let ergoc_inline_declarations bm ctxt decls =
  elift_context_fold_left (ergoc_inline_declaration bm) decls ctxt

(** val ergoc_inline_module :
    brand_model -> compilation_context -> ergoc_module ->
    (ergoc_module * compilation_context) eresult **)

let ergoc_inline_module bm ctxt mod0 =
  elift (fun res -> ({ modulec_annot = mod0.modulec_annot;
    modulec_namespace = mod0.modulec_namespace; modulec_declarations =
    (fst res) }, (snd res)))
    (ergoc_inline_declarations bm ctxt mod0.modulec_declarations)
