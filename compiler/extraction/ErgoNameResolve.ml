open Assoc
open Ast
open CTO
open CTOtoErgo
open Data
open Datatypes
open Ergo
open ErgoType
open List0
open Names
open NamespaceContext
open Provenance
open Result0
open String0

(** val namespace_ctxt_of_ergo_decls :
    namespace_ctxt -> namespace_name -> lrergo_declaration list ->
    namespace_name * namespace_ctxt **)

let rec namespace_ctxt_of_ergo_decls ctxt ns = function
| [] -> (ns, ctxt)
| l :: rest ->
  (match l with
   | DNamespace (_, ns') -> (ns', ctxt)
   | DType (prov, td) ->
     let ln = td.type_declaration_name in
     let an = absolute_name_of_local_name ns ln in
     let ef =
       match type_declaration_is_enum td.type_declaration_type with
       | Some enum_list ->
         let proc_enum = globals_from_enum prov (an, enum_list) in
         EnumType (map (fun xyz -> ((fst (fst xyz)), (snd xyz))) proc_enum)
       | None -> EnumNone
     in
     let (ns0, ctxt0) = namespace_ctxt_of_ergo_decls ctxt ns rest in
     (ns0, (add_type_to_namespace_ctxt ctxt0 ns0 ln an ef))
   | DConstant (_, ln, _, _) ->
     let an = absolute_name_of_local_name ns ln in
     let (ns0, ctxt0) = namespace_ctxt_of_ergo_decls ctxt ns rest in
     (ns0, (add_constant_to_namespace_ctxt ctxt0 ns0 ln EnumNone an))
   | DFunc (_, ln, _) ->
     let an = absolute_name_of_local_name ns ln in
     let (ns0, ctxt0) = namespace_ctxt_of_ergo_decls ctxt ns rest in
     (ns0, (add_function_to_namespace_ctxt ctxt0 ns0 ln an))
   | DContract (_, ln, _) ->
     let an = absolute_name_of_local_name ns ln in
     let (ns0, ctxt0) = namespace_ctxt_of_ergo_decls ctxt ns rest in
     (ns0, (add_contract_to_namespace_ctxt ctxt0 ns0 ln an))
   | _ -> namespace_ctxt_of_ergo_decls ctxt ns rest)

(** val namespace_ctxt_of_ergo_module :
    namespace_ctxt -> lrergo_module -> namespace_ctxt **)

let namespace_ctxt_of_ergo_module ctxt m =
  snd
    (namespace_ctxt_of_ergo_decls ctxt m.module_namespace
      m.module_declarations)

(** val namespace_ctxt_of_cto_packages :
    namespace_ctxt -> (provenance, relative_name) cto_package list ->
    namespace_ctxt **)

let namespace_ctxt_of_cto_packages ctxt ctos =
  let mls = map cto_package_to_ergo_module ctos in
  fold_left namespace_ctxt_of_ergo_module mls ctxt

(** val lookup_one_import :
    namespace_ctxt -> limport_decl -> namespace_table eresult **)

let lookup_one_import ctxt = function
| ImportAll (prov, ns) ->
  (match lookup string_dec ctxt.namespace_ctxt_modules ns with
   | Some tbl -> esuccess tbl []
   | None -> import_not_found_error prov ns)
| ImportSelf (_, ns) ->
  (match lookup string_dec ctxt.namespace_ctxt_modules ns with
   | Some tbl -> esuccess tbl []
   | None -> esuccess empty_namespace_table [])
| ImportName (prov, ns, ln) ->
  (match lookup string_dec ctxt.namespace_ctxt_modules ns with
   | Some tbl ->
     (match lookup string_dec tbl.namespace_table_types ln with
      | Some p ->
        let (an, e) = p in
        (match e with
         | EnumType l ->
           esuccess (import_one_enum_type_to_namespace_table ln an l) []
         | _ -> esuccess (import_one_type_to_namespace_table ln an) [])
      | None ->
        (match lookup string_dec tbl.namespace_table_constants ln with
         | Some an ->
           esuccess (import_one_constant_to_namespace_table ln (fst an)) []
         | None -> import_name_not_found_error prov ns ln))
   | None -> import_not_found_error prov ns)

(** val resolve_one_import :
    namespace_ctxt -> limport_decl -> namespace_ctxt eresult **)

let resolve_one_import ctxt ic =
  elift (fun tbl -> { namespace_ctxt_modules = ctxt.namespace_ctxt_modules;
    namespace_ctxt_namespace = ctxt.namespace_ctxt_namespace;
    namespace_ctxt_current_module = ctxt.namespace_ctxt_current_module;
    namespace_ctxt_current_in_scope =
    (namespace_table_app ctxt.namespace_ctxt_current_in_scope tbl);
    namespace_ctxt_abstract = ctxt.namespace_ctxt_abstract })
    (lookup_one_import ctxt ic)

(** val builtin_imports : char list list **)

let builtin_imports =
  accordproject_concerto_namespace :: (accordproject_stdlib_namespace :: [])

(** val is_builtin_import : namespace_name -> bool **)

let is_builtin_import ns =
  if in_dec string_dec ns builtin_imports then true else false

(** val stdlib_imports : char list list **)

let stdlib_imports =
  accordproject_concerto_namespace :: (accordproject_stdlib_namespace :: (accordproject_time_namespace :: (accordproject_options_namespace :: (accordproject_template_namespace :: []))))

(** val is_stdlib_import : namespace_name -> bool **)

let is_stdlib_import ns =
  if in_dec string_dec ns stdlib_imports then true else false

(** val resolve_ergo_type :
    namespace_ctxt -> lrergo_type -> laergo_type eresult **)

let rec resolve_ergo_type nsctxt = function
| ErgoTypeAny prov -> esuccess (ErgoTypeAny prov) []
| ErgoTypeNothing prov -> esuccess (ErgoTypeNothing prov) []
| ErgoTypeUnit prov -> esuccess (ErgoTypeUnit prov) []
| ErgoTypeBoolean prov -> esuccess (ErgoTypeBoolean prov) []
| ErgoTypeString prov -> esuccess (ErgoTypeString prov) []
| ErgoTypeDouble prov -> esuccess (ErgoTypeDouble prov) []
| ErgoTypeLong prov -> esuccess (ErgoTypeLong prov) []
| ErgoTypeInteger prov -> esuccess (ErgoTypeInteger prov) []
| ErgoTypeDateTimeFormat prov -> esuccess (ErgoTypeDateTimeFormat prov) []
| ErgoTypeDateTime prov -> esuccess (ErgoTypeDateTime prov) []
| ErgoTypeDuration prov -> esuccess (ErgoTypeDuration prov) []
| ErgoTypePeriod prov -> esuccess (ErgoTypePeriod prov) []
| ErgoTypeClassRef (prov, rn) ->
  elift (fun x -> ErgoTypeClassRef (prov, x))
    (resolve_type_name prov nsctxt rn)
| ErgoTypeOption (prov, t0) ->
  elift (fun x -> ErgoTypeOption (prov, x)) (resolve_ergo_type nsctxt t0)
| ErgoTypeRecord (prov, r) ->
  let initial_map =
    map (fun xy -> ((fst xy), (resolve_ergo_type nsctxt (snd xy)))) r
  in
  let lifted_map =
    emaplift (fun xy -> elift (fun t0 -> ((fst xy), t0)) (snd xy)) initial_map
  in
  elift (fun x -> ErgoTypeRecord (prov, x)) lifted_map
| ErgoTypeArray (prov, t0) ->
  elift (fun x -> ErgoTypeArray (prov, x)) (resolve_ergo_type nsctxt t0)
| ErgoTypeSum (prov, t1, t2) ->
  elift2 (fun x x0 -> ErgoTypeSum (prov, x, x0))
    (resolve_ergo_type nsctxt t1) (resolve_ergo_type nsctxt t2)

(** val resolve_ergo_type_struct :
    namespace_ctxt -> (char list * lrergo_type) list ->
    (char list * laergo_type) list eresult **)

let resolve_ergo_type_struct nsctxt t =
  emaplift (fun xy ->
    elift (fun t0 -> ((fst xy), t0)) (resolve_ergo_type nsctxt (snd xy))) t

(** val resolve_type_annotation :
    provenance -> namespace_ctxt -> relative_name option -> absolute_name
    option eresult **)

let resolve_type_annotation prov nsctxt = function
| Some rn -> elift (fun x -> Some x) (resolve_type_name prov nsctxt rn)
| None -> esuccess None []

(** val resolve_extends :
    provenance -> namespace_ctxt -> rextends -> aextends eresult **)

let resolve_extends =
  resolve_type_annotation

(** val resolve_ergo_type_signature :
    provenance -> namespace_ctxt -> char list -> lrergo_type_signature ->
    laergo_type_signature eresult **)

let resolve_ergo_type_signature prov nsctxt fname sig0 =
  let params_types =
    resolve_ergo_type_struct nsctxt sig0.type_signature_params
  in
  let params_types0 =
    eolift (fun ps ->
      duplicate_function_params_check prov fname (map fst ps) ps) params_types
  in
  let output_type =
    match sig0.type_signature_output with
    | Some out_ty -> elift (fun x -> Some x) (resolve_ergo_type nsctxt out_ty)
    | None -> esuccess None []
  in
  let emits_type =
    match sig0.type_signature_emits with
    | Some emits_ty ->
      elift (fun x -> Some x) (resolve_ergo_type nsctxt emits_ty)
    | None -> esuccess None []
  in
  elift3 (fun x x0 x1 -> { type_signature_annot = sig0.type_signature_annot;
    type_signature_params = x; type_signature_output = x0;
    type_signature_emits = x1 }) params_types0 output_type emits_type

(** val resolve_ergo_type_clauses :
    provenance -> namespace_ctxt -> (char list * lrergo_type_signature) list
    -> (char list * laergo_type_signature) list eresult **)

let resolve_ergo_type_clauses prov nsctxt cls =
  emaplift (fun xy ->
    elift (fun r -> ((fst xy), r))
      (resolve_ergo_type_signature prov nsctxt (fst xy) (snd xy))) cls

(** val resolve_ergo_type_declaration_desc :
    provenance -> namespace_ctxt -> char list -> lrergo_type_declaration_desc
    -> laergo_type_declaration_desc eresult **)

let resolve_ergo_type_declaration_desc prov nsctxt name = function
| ErgoTypeEnum l -> esuccess (ErgoTypeEnum l) []
| ErgoTypeTransaction (isabs, extends_name, ergo_type_struct) ->
  elift2 (fun x x0 -> ErgoTypeTransaction (isabs, x, x0))
    (resolve_extends prov nsctxt extends_name)
    (resolve_ergo_type_struct nsctxt ergo_type_struct)
| ErgoTypeConcept (isabs, extends_name, ergo_type_struct) ->
  elift2 (fun x x0 -> ErgoTypeConcept (isabs, x, x0))
    (resolve_extends prov nsctxt extends_name)
    (resolve_ergo_type_struct nsctxt ergo_type_struct)
| ErgoTypeEvent (isabs, extends_name, ergo_type_struct) ->
  elift2 (fun x x0 -> ErgoTypeEvent (isabs, x, x0))
    (resolve_extends prov nsctxt extends_name)
    (resolve_ergo_type_struct nsctxt ergo_type_struct)
| ErgoTypeAsset (isabs, extends_name, ergo_type_struct) ->
  elift2 (fun x x0 -> ErgoTypeAsset (isabs, x, x0))
    (resolve_extends prov nsctxt extends_name)
    (resolve_ergo_type_struct nsctxt ergo_type_struct)
| ErgoTypeParticipant (isabs, extends_name, ergo_type_struct) ->
  elift2 (fun x x0 -> ErgoTypeParticipant (isabs, x, x0))
    (resolve_extends prov nsctxt extends_name)
    (resolve_ergo_type_struct nsctxt ergo_type_struct)
| ErgoTypeGlobal ergo_type ->
  elift (fun x -> ErgoTypeGlobal x) (resolve_ergo_type nsctxt ergo_type)
| ErgoTypeFunction ergo_type_signature ->
  elift (fun x -> ErgoTypeFunction x)
    (resolve_ergo_type_signature prov nsctxt name ergo_type_signature)
| ErgoTypeContract (template_type, state_type, clauses_sigs) ->
  elift3 (fun x x0 x1 -> ErgoTypeContract (x, x0, x1))
    (resolve_ergo_type nsctxt template_type)
    (resolve_ergo_type nsctxt state_type)
    (resolve_ergo_type_clauses prov nsctxt clauses_sigs)

(** val resolve_ergo_type_declaration :
    provenance -> namespace_name -> namespace_ctxt ->
    (abstract_ctxt * lrergo_type_declaration) ->
    ((abstract_ctxt * laergo_declaration) * ((char list * laergo_expr) * data)
    list) eresult **)

let resolve_ergo_type_declaration prov module_ns nsctxt = function
| (actxt, decl0) ->
  let name = absolute_name_of_local_name module_ns decl0.type_declaration_name
  in
  let enumglobals =
    match type_declaration_is_enum decl0.type_declaration_type with
    | Some enum_list -> globals_from_enum prov (name, enum_list)
    | None -> []
  in
  let actxt0 =
    if type_declaration_is_abstract decl0.type_declaration_type
    then name :: actxt
    else actxt
  in
  let edecl_desc =
    resolve_ergo_type_declaration_desc decl0.type_declaration_annot nsctxt
      decl0.type_declaration_name decl0.type_declaration_type
  in
  elift (fun k -> ((actxt0, (DType (prov, { type_declaration_annot =
    decl0.type_declaration_annot; type_declaration_name = name;
    type_declaration_type = k }))), enumglobals)) edecl_desc

(** val resolve_ergo_pattern :
    namespace_ctxt -> lrergo_pattern -> laergo_pattern eresult **)

let resolve_ergo_pattern nsctxt = function
| CaseData (prov, d) -> esuccess (CaseData (prov, d)) []
| CaseEnum (prov, v) ->
  let ename = resolve_econstant_name prov nsctxt v in
  elift (fun x -> CaseData (prov, x)) (elift snd ename)
| CaseWildcard (prov, ta) ->
  elift (fun x -> CaseWildcard (prov, x))
    (resolve_type_annotation prov nsctxt ta)
| CaseLet (prov, v, ta) ->
  elift (fun x -> CaseLet (prov, v, x))
    (resolve_type_annotation prov nsctxt ta)
| CaseLetOption (prov, v, ta) ->
  elift (fun x -> CaseLetOption (prov, v, x))
    (resolve_type_annotation prov nsctxt ta)

(** val resolve_ergo_expr :
    namespace_ctxt -> lrergo_expr -> laergo_expr eresult **)

let rec resolve_ergo_expr nsctxt = function
| EThis prov -> esuccess (EThis prov) []
| EThisContract prov -> esuccess (EThisContract prov) []
| EThisClause prov -> esuccess (EThisClause prov) []
| EThisState prov -> esuccess (EThisState prov) []
| EVar (prov, r) ->
  let (n, v) = r in
  (match n with
   | Some ns ->
     let cname = resolve_all_constant_name prov nsctxt ((Some ns), v) in
     elift (fun x -> EVar (prov, x)) cname
   | None ->
     let cname = resolve_all_constant_name prov nsctxt (None, v) in
     elift_both (fun x -> esuccess (EVar (prov, x)) []) (fun _ ->
       esuccess (EVar (prov, v)) []) cname)
| EConst (prov, d) -> esuccess (EConst (prov, d)) []
| EText (prov, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e0) acc
  in
  elift (fun x -> EText (prov, x)) (fold_right proc_one init_el el)
| ENone prov -> esuccess (ENone prov) []
| ESome (prov, e0) ->
  elift (fun x -> ESome (prov, x)) (resolve_ergo_expr nsctxt e0)
| EArray (prov, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e0) acc
  in
  elift (fun x -> EArray (prov, x)) (fold_right proc_one init_el el)
| EUnaryOperator (prov, u, e0) ->
  elift (fun x -> EUnaryOperator (prov, u, x)) (resolve_ergo_expr nsctxt e0)
| EBinaryOperator (prov, b, e1, e2) ->
  elift2 (fun x x0 -> EBinaryOperator (prov, b, x, x0))
    (resolve_ergo_expr nsctxt e1) (resolve_ergo_expr nsctxt e2)
| EUnaryBuiltin (prov, u, e0) ->
  elift (fun x -> EUnaryBuiltin (prov, u, x)) (resolve_ergo_expr nsctxt e0)
| EBinaryBuiltin (prov, b, e1, e2) ->
  elift2 (fun x x0 -> EBinaryBuiltin (prov, b, x, x0))
    (resolve_ergo_expr nsctxt e1) (resolve_ergo_expr nsctxt e2)
| EIf (prov, e1, e2, e3) ->
  elift3 (fun x x0 x1 -> EIf (prov, x, x0, x1)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_expr nsctxt e2) (resolve_ergo_expr nsctxt e3)
| ELet (prov, v, ta, e1, e2) ->
  let rta =
    match ta with
    | Some ta0 -> elift (fun x -> Some x) (resolve_ergo_type nsctxt ta0)
    | None -> esuccess None []
  in
  elift3 (fun x x0 x1 -> ELet (prov, v, x, x0, x1)) rta
    (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_expr (hide_constant_from_namespace_ctxt_current nsctxt v)
      e2)
| EPrint (prov, e1, e2) ->
  elift2 (fun x x0 -> EPrint (prov, x, x0)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_expr nsctxt e2)
| ERecord (prov, el) ->
  let init_rec = esuccess [] [] in
  let proc_one = fun att acc ->
    let attname = fst att in
    let e0 = resolve_ergo_expr nsctxt (snd att) in
    elift2 (fun e1 acc0 -> (attname, e1) :: acc0) e0 acc
  in
  elift (fun x -> ERecord (prov, x)) (fold_right proc_one init_rec el)
| ENew (prov, cr, el) ->
  let rcr = resolve_type_name prov nsctxt cr in
  let init_rec = esuccess [] [] in
  let proc_one = fun att acc ->
    let attname = fst att in
    let e0 = resolve_ergo_expr nsctxt (snd att) in
    elift2 (fun e1 acc0 -> (attname, e1) :: acc0) e0 acc
  in
  elift2 (fun x x0 -> ENew (prov, x, x0)) rcr
    (fold_right proc_one init_rec el)
| ECallFun (prov, fname, el) ->
  let rfname = resolve_function_name prov nsctxt fname in
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e0) acc
  in
  elift2 (fun x x0 -> ECallFun (prov, x, x0)) rfname
    (fold_right proc_one init_el el)
| ECallFunInGroup (prov, gname, fname, el) ->
  let rgname = resolve_contract_name prov nsctxt gname in
  let init_el = esuccess [] [] in
  let proc_one = fun e0 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e0) acc
  in
  elift3 (fun x x0 x1 -> ECallFunInGroup (prov, x, x0, x1)) rgname
    (esuccess fname []) (fold_right proc_one init_el el)
| EMatch (prov, e0, ecases, edefault) ->
  let ec0 = resolve_ergo_expr nsctxt e0 in
  let eccases =
    let proc_one = fun acc ecase ->
      let (pcase, pe) = ecase in
      let apcase = resolve_ergo_pattern nsctxt pcase in
      eolift (fun apcase0 ->
        eolift (fun acc0 ->
          elift (fun x -> (apcase0, x) :: acc0) (resolve_ergo_expr nsctxt pe))
          acc) apcase
    in
    fold_left proc_one ecases (esuccess [] [])
  in
  let ecdefault = resolve_ergo_expr nsctxt edefault in
  eolift (fun ec1 ->
    eolift (fun eccases0 ->
      elift (fun ecdefault0 -> EMatch (prov, ec1, eccases0, ecdefault0))
        ecdefault) eccases) ec0
| EForeach (prov, foreachs, econd, e2) ->
  let re2 = resolve_ergo_expr nsctxt e2 in
  let recond =
    match econd with
    | Some econd0 -> elift (fun x -> Some x) (resolve_ergo_expr nsctxt econd0)
    | None -> esuccess None []
  in
  let init_e = esuccess [] [] in
  let proc_one = fun foreach acc ->
    let v = fst foreach in
    let e0 = resolve_ergo_expr nsctxt (snd foreach) in
    elift2 (fun e1 acc0 -> (v, e1) :: acc0) e0 acc
  in
  elift3 (fun x x0 x1 -> EForeach (prov, x, x0, x1))
    (fold_right proc_one init_e foreachs) recond re2
| EAs (prov, f, e0) ->
  elift (fun x -> EAs (prov, f, x)) (resolve_ergo_expr nsctxt e0)

(** val resolve_ergo_stmt :
    namespace_ctxt -> lrergo_stmt -> laergo_stmt eresult **)

let rec resolve_ergo_stmt nsctxt = function
| SReturn (prov, e0) ->
  elift (fun x -> SReturn (prov, x)) (resolve_ergo_expr nsctxt e0)
| SFunReturn (prov, e0) ->
  elift (fun x -> SFunReturn (prov, x)) (resolve_ergo_expr nsctxt e0)
| SThrow (prov, e0) ->
  elift (fun x -> SThrow (prov, x)) (resolve_ergo_expr nsctxt e0)
| SCallClause (prov, e0, fname, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e1 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e1) acc
  in
  elift3 (fun x x0 x1 -> SCallClause (prov, x, x0, x1))
    (resolve_ergo_expr nsctxt e0) (esuccess fname [])
    (fold_right proc_one init_el el)
| SCallContract (prov, e0, el) ->
  let init_el = esuccess [] [] in
  let proc_one = fun e1 acc ->
    elift2 (fun x x0 -> x :: x0) (resolve_ergo_expr nsctxt e1) acc
  in
  elift2 (fun x x0 -> SCallContract (prov, x, x0))
    (resolve_ergo_expr nsctxt e0) (fold_right proc_one init_el el)
| SSetState (prov, e1, s2) ->
  elift2 (fun x x0 -> SSetState (prov, x, x0)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_stmt nsctxt s2)
| SSetStateDot (prov, a, e1, s2) ->
  elift2 (fun x x0 -> SSetStateDot (prov, a, x, x0))
    (resolve_ergo_expr nsctxt e1) (resolve_ergo_stmt nsctxt s2)
| SEmit (prov, e1, s2) ->
  elift2 (fun x x0 -> SEmit (prov, x, x0)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_stmt nsctxt s2)
| SLet (prov, v, ta, e1, s2) ->
  let rta =
    match ta with
    | Some ta0 -> elift (fun x -> Some x) (resolve_ergo_type nsctxt ta0)
    | None -> esuccess None []
  in
  elift3 (fun x x0 x1 -> SLet (prov, v, x, x0, x1)) rta
    (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_stmt (hide_constant_from_namespace_ctxt_current nsctxt v)
      s2)
| SPrint (prov, e1, s2) ->
  elift2 (fun x x0 -> SPrint (prov, x, x0)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_stmt nsctxt s2)
| SIf (prov, e1, s2, s3) ->
  elift3 (fun x x0 x1 -> SIf (prov, x, x0, x1)) (resolve_ergo_expr nsctxt e1)
    (resolve_ergo_stmt nsctxt s2) (resolve_ergo_stmt nsctxt s3)
| SEnforce (prov, e1, os2, s3) ->
  let rs2 =
    match os2 with
    | Some s2 -> elift (fun x -> Some x) (resolve_ergo_stmt nsctxt s2)
    | None -> esuccess None []
  in
  elift3 (fun x x0 x1 -> SEnforce (prov, x, x0, x1))
    (resolve_ergo_expr nsctxt e1) rs2 (resolve_ergo_stmt nsctxt s3)
| SMatch (prov, e0, scases, sdefault) ->
  let ec0 = resolve_ergo_expr nsctxt e0 in
  let sccases =
    let proc_one = fun acc scase ->
      let (pcase, pe) = scase in
      let apcase = resolve_ergo_pattern nsctxt pcase in
      eolift (fun apcase0 ->
        eolift (fun acc0 ->
          elift (fun x -> (apcase0, x) :: acc0) (resolve_ergo_stmt nsctxt pe))
          acc) apcase
    in
    fold_left proc_one scases (esuccess [] [])
  in
  let scdefault = resolve_ergo_stmt nsctxt sdefault in
  eolift (fun ec1 ->
    eolift (fun sccases0 ->
      elift (fun scdefault0 -> SMatch (prov, ec1, sccases0, scdefault0))
        scdefault) sccases) ec0

(** val resolve_ergo_function :
    namespace_name -> namespace_ctxt -> char list -> lrergo_function ->
    laergo_function eresult **)

let resolve_ergo_function _ nsctxt name f =
  let prov = f.function_annot in
  let sig0 = f.function_sig in
  let params = map fst sig0.type_signature_params in
  let nsctxt0 = hide_constants_from_namespace_ctxt_current nsctxt params in
  let rbody =
    match f.function_body with
    | Some body -> elift (fun x -> Some x) (resolve_ergo_expr nsctxt0 body)
    | None -> esuccess None []
  in
  elift2 (fun x x0 -> { function_annot = prov; function_sig = x;
    function_body = x0 })
    (resolve_ergo_type_signature prov nsctxt0 name sig0) rbody

(** val resolve_ergo_clause :
    namespace_name -> namespace_ctxt -> (provenance, provenance,
    relative_name) ergo_clause -> laergo_clause eresult **)

let resolve_ergo_clause _ nsctxt c =
  let prov = c.clause_annot in
  let rcname = c.clause_name in
  let rbody =
    match c.clause_body with
    | Some body -> elift (fun x -> Some x) (resolve_ergo_stmt nsctxt body)
    | None -> esuccess None []
  in
  elift2 (fun x x0 -> { clause_annot = prov; clause_name = rcname;
    clause_sig = x; clause_body = x0 })
    (resolve_ergo_type_signature prov nsctxt rcname c.clause_sig) rbody

(** val resolve_ergo_clauses :
    namespace_name -> namespace_ctxt -> (provenance, provenance,
    relative_name) ergo_clause list -> laergo_clause list eresult **)

let resolve_ergo_clauses module_ns nsctxt cl =
  emaplift (resolve_ergo_clause module_ns nsctxt) cl

(** val resolve_ergo_contract :
    namespace_name -> namespace_ctxt -> lrergo_contract -> laergo_contract
    eresult **)

let resolve_ergo_contract module_ns nsctxt c =
  let prov = c.contract_annot in
  let rtemplate = resolve_ergo_type nsctxt c.contract_template in
  let rstate =
    match c.contract_state with
    | Some state -> elift (fun x -> Some x) (resolve_ergo_type nsctxt state)
    | None -> esuccess None []
  in
  elift3 (fun x x0 x1 -> { contract_annot = prov; contract_template = x;
    contract_state = x0; contract_clauses = x1 }) rtemplate rstate
    (resolve_ergo_clauses module_ns nsctxt c.contract_clauses)

(** val resolve_ergo_declaration :
    namespace_ctxt -> lrergo_declaration -> (laergo_declaration
    list * namespace_ctxt) eresult **)

let resolve_ergo_declaration nsctxt decl =
  let module_ns = nsctxt.namespace_ctxt_namespace in
  let actxt = nsctxt.namespace_ctxt_abstract in
  (match decl with
   | DNamespace (prov, ns) ->
     esuccess (((DNamespace (prov, ns)) :: []),
       (local_namespace_scope nsctxt ns)) []
   | DImport (prov, id) ->
     elift (fun x -> (((DImport (prov, id)) :: []), x))
       (resolve_one_import nsctxt id)
   | DType (prov, td) ->
     let ln = td.type_declaration_name in
     let an = absolute_name_of_local_name module_ns ln in
     let ef =
       match type_declaration_is_enum td.type_declaration_type with
       | Some enum_list ->
         let proc_enum = globals_from_enum prov (an, enum_list) in
         EnumType (map (fun xyz -> ((fst (fst xyz)), (snd xyz))) proc_enum)
       | None -> EnumNone
     in
     let nsctxt0 = add_type_to_namespace_ctxt_current nsctxt ln an ef in
     elift (fun xy ->
       let (p, globalenums) = xy in
       let (actxt0, x) = p in
       let nsctxt1 = update_namespace_context_abstract nsctxt0 actxt0 in
       let enum_ns = enum_namespace module_ns ln in
       let (rglobalnames, rglobalenums) =
         split
           (map (fun xyz ->
             let (p0, d) = xyz in
             let (en, expr) = p0 in
             let an0 = absolute_name_of_local_name enum_ns en in
             ((en, (an0, (EnumValue d))), (DConstant (prov, an0, None, expr))))
             globalenums)
       in
       let nsctxt2 =
         add_econstants_to_namespace_ctxt_current nsctxt1 enum_ns rglobalnames
       in
       ((x :: rglobalenums), nsctxt2))
       (resolve_ergo_type_declaration prov module_ns nsctxt0 (actxt, td))
   | DStmt (prov, st) ->
     elift (fun x -> (((DStmt (prov, x)) :: []), nsctxt))
       (resolve_ergo_stmt nsctxt st)
   | DConstant (prov, ln, ta, e) ->
     let an = absolute_name_of_local_name module_ns ln in
     let rta =
       match ta with
       | Some ta0 -> elift (fun x -> Some x) (resolve_ergo_type nsctxt ta0)
       | None -> esuccess None []
     in
     let nsctxt0 =
       add_constant_to_namespace_ctxt_current nsctxt ln an EnumNone
     in
     elift2 (fun ta0 x -> (((DConstant (prov, an, ta0, x)) :: []), nsctxt0))
       rta (resolve_ergo_expr nsctxt0 e)
   | DFunc (prov, ln, fd) ->
     let an = absolute_name_of_local_name module_ns ln in
     let nsctxt0 = add_function_to_namespace_ctxt_current nsctxt ln an in
     elift (fun x -> (((DFunc (prov, an, x)) :: []), nsctxt0))
       (resolve_ergo_function module_ns nsctxt0 an fd)
   | DContract (prov, ln, c) ->
     let an = absolute_name_of_local_name module_ns ln in
     let nsctxt0 = add_contract_to_namespace_ctxt_current nsctxt ln an in
     elift (fun x -> (((DContract (prov, an, x)) :: []), nsctxt0))
       (resolve_ergo_contract module_ns nsctxt0 c)
   | DSetContract (prov, rn, e1) ->
     eolift (fun an ->
       elift (fun x -> (((DSetContract (prov, an, x)) :: []), nsctxt))
         (resolve_ergo_expr nsctxt e1)) (resolve_contract_name prov nsctxt rn))

(** val resolve_ergo_template_expr :
    namespace_ctxt -> lrergo_expr -> laergo_expr eresult **)

let resolve_ergo_template_expr =
  resolve_ergo_expr

(** val resolve_ergo_declarations :
    namespace_ctxt -> lrergo_declaration list -> ((provenance, provenance,
    absolute_name) ergo_declaration list * namespace_ctxt) eresult **)

let resolve_ergo_declarations ctxt decls =
  elift (fun xy -> ((List0.concat (fst xy)), (snd xy)))
    (elift_context_fold_left resolve_ergo_declaration decls ctxt)

(** val silently_resolve_ergo_declarations :
    namespace_ctxt -> lrergo_declaration list -> namespace_ctxt eresult **)

let silently_resolve_ergo_declarations ctxt decls =
  elift snd (resolve_ergo_declarations ctxt decls)

(** val init_namespace_ctxt : namespace_ctxt **)

let init_namespace_ctxt =
  empty_namespace_ctxt no_namespace

(** val patch_cto_imports :
    namespace_name -> lrergo_declaration list -> lrergo_declaration list **)

let patch_cto_imports ctxt_ns decls =
  if is_builtin_import ctxt_ns
  then (DImport (dummy_provenance, (ImportSelf (dummy_provenance,
         ctxt_ns)))) :: decls
  else (DImport (dummy_provenance, (ImportAll (dummy_provenance,
         accordproject_concerto_namespace)))) :: ((DImport (dummy_provenance,
         (ImportSelf (dummy_provenance, ctxt_ns)))) :: decls)

(** val patch_ergo_imports :
    namespace_name -> lrergo_declaration list -> lrergo_declaration list **)

let patch_ergo_imports ctxt_ns decls =
  if is_builtin_import ctxt_ns
  then app decls ((DImport (dummy_provenance, (ImportSelf (dummy_provenance,
         ctxt_ns)))) :: [])
  else (DImport (dummy_provenance, (ImportAll (dummy_provenance,
         accordproject_concerto_namespace)))) :: ((DImport (dummy_provenance,
         (ImportAll (dummy_provenance,
         accordproject_stdlib_namespace)))) :: ((DImport (dummy_provenance,
         (ImportSelf (dummy_provenance, ctxt_ns)))) :: decls))

(** val new_ergo_module_namespace :
    namespace_ctxt -> namespace_name -> namespace_ctxt eresult **)

let new_ergo_module_namespace ctxt ns =
  if is_builtin_import ns
  then esuccess ctxt []
  else let builtin_cto_imports = (DImport (dummy_provenance, (ImportAll
         (dummy_provenance, accordproject_concerto_namespace)))) :: ((DImport
         (dummy_provenance, (ImportAll (dummy_provenance,
         accordproject_stdlib_namespace)))) :: ((DImport (dummy_provenance,
         (ImportSelf (dummy_provenance, ns)))) :: []))
       in
       let ctxt0 = new_namespace_scope ctxt ns in
       silently_resolve_ergo_declarations ctxt0 builtin_cto_imports

(** val resolve_cto_package :
    namespace_ctxt -> lrcto_package -> (laergo_module * namespace_ctxt)
    eresult **)

let resolve_cto_package ctxt cto =
  let m = cto_package_to_ergo_module cto in
  let module_ns = m.module_namespace in
  let ctxt0 = new_namespace_scope ctxt module_ns in
  let ctxt1 = namespace_ctxt_of_ergo_module ctxt0 m in
  let declarations = m.module_declarations in
  elift (fun nc -> ({ module_annot = m.module_annot; module_file =
    m.module_file; module_prefix = m.module_prefix; module_namespace =
    module_ns; module_declarations = (fst nc) }, (snd nc)))
    (resolve_ergo_declarations ctxt1
      (patch_cto_imports module_ns declarations))

(** val resolve_ergo_module :
    namespace_ctxt -> lrergo_module -> (laergo_module * namespace_ctxt)
    eresult **)

let resolve_ergo_module ctxt m =
  let module_ns = m.module_namespace in
  let ctxt0 = new_namespace_scope ctxt module_ns in
  let declarations = m.module_declarations in
  elift (fun nc -> ({ module_annot = m.module_annot; module_file =
    m.module_file; module_prefix = m.module_prefix; module_namespace =
    module_ns; module_declarations = (fst nc) }, (snd nc)))
    (resolve_ergo_declarations ctxt0
      (patch_ergo_imports module_ns declarations))

(** val resolve_ergo_template :
    namespace_ctxt -> (char list * lrergo_expr) list ->
    (char list * laergo_expr) list eresult **)

let resolve_ergo_template ctxt ftemplate =
  elift_fold_left (fun acc template ->
    let fname = fst template in
    let template0 = snd template in
    elift (fun x -> (fname, x) :: acc)
      (resolve_ergo_template_expr ctxt template0)) ftemplate []

(** val resolve_ergo_modules :
    namespace_ctxt -> lrergo_module list -> (laergo_module
    list * namespace_ctxt) eresult **)

let resolve_ergo_modules ctxt ml =
  elift_context_fold_left resolve_ergo_module ml ctxt

(** val resolve_cto_packages :
    namespace_ctxt -> lrcto_package list -> (laergo_module
    list * namespace_ctxt) eresult **)

let resolve_cto_packages ctxt ctos =
  let ctxt0 = namespace_ctxt_of_cto_packages ctxt ctos in
  elift_context_fold_left resolve_cto_package ctos ctxt0

(** val triage_ctos_and_ergos :
    lrergo_input list -> (lrcto_package list * lrergo_module
    list) * lrergo_module option **)

let rec triage_ctos_and_ergos = function
| [] -> (([], []), None)
| l :: rest ->
  (match l with
   | InputErgo ml ->
     let (p, p') = triage_ctos_and_ergos rest in
     let (ctos', rest') = p in
     (match p' with
      | Some _ -> ((ctos', (ml :: rest')), p')
      | None ->
        if is_stdlib_import ml.module_namespace
        then ((ctos', (ml :: rest')), None)
        else ((ctos', rest'), (Some ml)))
   | InputCTO cto ->
     let (p, p') = triage_ctos_and_ergos rest in
     let (ctos', rest') = p in (((cto :: ctos'), rest'), p'))
