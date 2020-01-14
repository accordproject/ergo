open Ast
open Data
open Datatypes
open Ergo
open ErgoC
open ErgoCSugar
open ErgoType
open List0
open Names
open Provenance
open QLib
open Result0
open String0
open UnaryOperators

(** val create_call :
    provenance -> char list -> char list -> char list -> ergoc_expr ->
    ergoc_expr list -> (char list * laergo_type) list -> ergoc_expr eresult **)

let create_call prov coname clname v0 effparam0 effparamrest callparams =
  let zipped = zip callparams (effparam0 :: effparamrest) in
  (match zipped with
   | Some _ ->
     esuccess
       (coq_ECallClause prov coname clname ((EVar (prov,
         v0)) :: effparamrest)) []
   | None -> main_parameter_mismatch_error prov)

(** val case_of_sig :
    provenance -> char list -> char list -> ergoc_expr -> ergoc_expr list ->
    (char list * sigc) -> (absolute_name * ((provenance, absolute_name)
    ergo_pattern * ergoc_expr)) list eresult **)

let case_of_sig prov coname v0 effparam0 effparamrest s =
  let clname = fst s in
  let callparams = (snd s).sigc_params in
  (match callparams with
   | [] -> main_at_least_one_parameter_error prov
   | _ :: l ->
     (match l with
      | [] -> esuccess [] []
      | _ :: l0 ->
        (match l0 with
         | [] -> esuccess [] []
         | _ :: l1 ->
           (match l1 with
            | [] -> esuccess [] []
            | p :: otherparams ->
              let (param0, et) = p in
              (match et with
               | ErgoTypeClassRef (_, type0) ->
                 let prunedcallparams = (param0, et) :: otherparams in
                 elift (fun x -> (type0, ((CaseLet (prov, v0, (Some type0))),
                   x)) :: [])
                   (create_call prov coname clname v0 effparam0 effparamrest
                     prunedcallparams)
               | _ -> esuccess [] [])))))

(** val make_cases :
    laergo_type_declaration list -> provenance ->
    (absolute_name * (laergo_pattern * ergoc_expr)) list ->
    (laergo_pattern * ergoc_expr) list eresult **)

let make_cases order prov xy =
  let oxy = sort_given_topo_order order fst xy in
  duplicate_clause_for_request_check prov (map fst oxy) (map snd oxy)

(** val match_of_sigs :
    laergo_type_declaration list -> provenance -> char list -> char list ->
    ergoc_expr -> ergoc_expr list -> (char list * sigc) list -> ergoc_expr
    eresult **)

let match_of_sigs order prov coname v0 effparam0 effparamrest ss =
  eolift (fun xy ->
    let ecases = make_cases order prov xy in
    elift (fun cases -> EMatch (prov, effparam0, cases,
      (coq_EFailure prov (EConst (prov, (default_match_error_content prov))))))
      ecases)
    (eflatmaplift (case_of_sig prov coname v0 effparam0 effparamrest) ss)

(** val match_of_sigs_top :
    laergo_type_declaration list -> provenance -> char list -> ergoc_expr
    list -> (char list * sigc) list -> ergoc_expr eresult **)

let match_of_sigs_top order prov coname effparams ss =
  match effparams with
  | [] -> main_at_least_one_parameter_error prov
  | effparam0 :: effparamrest ->
    let v0 = append ('$'::[]) clause_main_name in
    match_of_sigs order prov coname v0 effparam0 effparamrest ss

(** val filter_init : (char list * sigc) list -> (char list * sigc) list **)

let filter_init sigs =
  filter (fun s ->
    if string_dec (fst s) clause_init_name then false else true) sigs

(** val create_main_clause_for_contract :
    laergo_type_declaration list -> provenance -> char list -> ergoc_contract
    -> (local_name * ergoc_function) eresult **)

let create_main_clause_for_contract order prov coname c =
  let sigs = lookup_contractc_request_signatures c in
  let sigs0 = filter_init sigs in
  let effparams = (EVar (prov,
    ('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))) :: []
  in
  let template = c.contractc_template in
  let params = (('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))),
    (ErgoTypeClassRef (prov, default_request_absolute_name))) :: []
  in
  let state = c.contractc_state in
  elift
    (coq_EClauseAsFunction prov clause_main_name template None state None
      params)
    (elift (fun x -> Some x)
      (match_of_sigs_top order prov coname effparams sigs0))

(** val default_state : provenance -> ergoc_expr **)

let default_state prov =
  EUnaryBuiltin (prov, (OpBrand (default_state_absolute_name :: [])), (EConst
    (prov, (Coq_drec []))))

(** val create_init_clause_for_contract :
    provenance -> ergoc_contract -> local_name * ergoc_function **)

let create_init_clause_for_contract prov c =
  let template = c.contractc_template in
  let state = c.contractc_state in
  let params = [] in
  let init_body =
    setState prov (default_state prov)
      (coq_EReturn prov (EConst (prov, Coq_dunit)))
  in
  coq_EClauseAsFunction prov clause_init_name template None state None params
    (Some init_body)

(** val add_init_clause_to_contract : ergoc_contract -> ergoc_contract **)

let add_init_clause_to_contract c =
  let prov = c.contractc_annot in
  if in_dec string_dec clause_init_name (map fst c.contractc_clauses)
  then c
  else let init_clause = create_init_clause_for_contract prov c in
       { contractc_annot = prov; contractc_template = c.contractc_template;
       contractc_state = c.contractc_state; contractc_clauses =
       (app c.contractc_clauses (init_clause :: [])) }

(** val add_main_clause_to_contract :
    laergo_type_declaration list -> char list -> ergoc_contract ->
    ergoc_contract eresult **)

let add_main_clause_to_contract order coname c =
  let prov = c.contractc_annot in
  if in_dec string_dec clause_main_name (map fst c.contractc_clauses)
  then esuccess c []
  else elift (fun main_clause -> { contractc_annot = prov;
         contractc_template = c.contractc_template; contractc_state =
         c.contractc_state; contractc_clauses =
         (app c.contractc_clauses (main_clause :: [])) })
         (create_main_clause_for_contract order prov coname c)

(** val ergoc_expand_declaration :
    laergo_type_declaration list -> ergoc_declaration -> ergoc_declaration
    eresult **)

let ergoc_expand_declaration order d = match d with
| DCContract (prov, cn, c) ->
  let cd = add_init_clause_to_contract c in
  elift (fun dd -> DCContract (prov, cn, dd))
    (add_main_clause_to_contract order cn cd)
| _ -> esuccess d []

(** val ergoc_expand_declarations :
    laergo_type_declaration list -> ergoc_declaration list ->
    ergoc_declaration list eresult **)

let ergoc_expand_declarations order dl =
  emaplift (ergoc_expand_declaration order) dl

(** val ergoc_expand_module :
    laergo_type_declaration list -> ergoc_module -> ergoc_module eresult **)

let ergoc_expand_module order p =
  elift (fun ds -> { modulec_annot = p.modulec_annot; modulec_namespace =
    p.modulec_namespace; modulec_declarations = ds })
    (ergoc_expand_declarations order p.modulec_declarations)
