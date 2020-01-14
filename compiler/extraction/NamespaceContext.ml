open Assoc
open Data
open Datatypes
open List0
open Names
open Provenance
open Result0
open String0

type enum_flag =
| EnumNone
| EnumValue of data
| EnumType of (char list * data) list

type name_table = (local_name * (absolute_name * enum_flag)) list

type namespace_table = { namespace_table_types : name_table;
                         namespace_table_constants : name_table;
                         namespace_table_functions : name_table;
                         namespace_table_contracts : name_table }

(** val empty_namespace_table : namespace_table **)

let empty_namespace_table =
  { namespace_table_types = []; namespace_table_constants = [];
    namespace_table_functions = []; namespace_table_contracts = [] }

(** val import_one_type_to_namespace_table :
    local_name -> absolute_name -> namespace_table **)

let import_one_type_to_namespace_table ln an =
  { namespace_table_types = ((ln, (an, EnumNone)) :: []);
    namespace_table_constants = []; namespace_table_functions = [];
    namespace_table_contracts = [] }

(** val import_one_enum_type_to_namespace_table :
    local_name -> absolute_name -> (char list * data) list -> namespace_table **)

let import_one_enum_type_to_namespace_table ln an el =
  let cs =
    map (fun ef ->
      let (ename, d) = ef in
      (ename, ((absolute_name_of_local_name an ename), (EnumValue d)))) el
  in
  { namespace_table_types = ((ln, (an, (EnumType el))) :: []);
  namespace_table_constants = cs; namespace_table_functions = [];
  namespace_table_contracts = [] }

(** val import_one_constant_to_namespace_table :
    local_name -> absolute_name -> namespace_table **)

let import_one_constant_to_namespace_table ln an =
  { namespace_table_types = []; namespace_table_constants = ((ln, (an,
    EnumNone)) :: []); namespace_table_functions = [];
    namespace_table_contracts = [] }

(** val namespace_table_app :
    namespace_table -> namespace_table -> namespace_table **)

let namespace_table_app tbl1 tbl2 =
  { namespace_table_types =
    (app tbl1.namespace_table_types tbl2.namespace_table_types);
    namespace_table_constants =
    (app tbl1.namespace_table_constants tbl2.namespace_table_constants);
    namespace_table_functions =
    (app tbl1.namespace_table_functions tbl2.namespace_table_functions);
    namespace_table_contracts =
    (app tbl1.namespace_table_contracts tbl2.namespace_table_contracts) }

(** val lookup_type_name :
    provenance -> namespace_table -> local_name -> absolute_name eresult **)

let lookup_type_name prov tbl ln =
  match lookup string_dec tbl.namespace_table_types ln with
  | Some an -> esuccess (fst an) []
  | None -> type_name_not_found_error prov ln

(** val lookup_constant_name :
    provenance -> namespace_table -> local_name -> absolute_name eresult **)

let lookup_constant_name prov tbl ln =
  match lookup string_dec tbl.namespace_table_constants ln with
  | Some p ->
    let (an, e) = p in
    (match e with
     | EnumNone -> esuccess an []
     | _ -> variable_name_not_found_error prov ln)
  | None -> variable_name_not_found_error prov ln

(** val lookup_econstant_name :
    provenance -> namespace_table -> local_name -> (absolute_name * data)
    eresult **)

let lookup_econstant_name prov tbl ln =
  match lookup string_dec tbl.namespace_table_constants ln with
  | Some p ->
    let (an, e) = p in
    (match e with
     | EnumValue d -> esuccess (an, d) []
     | _ -> enum_name_not_found_error prov ln)
  | None -> enum_name_not_found_error prov ln

(** val lookup_function_name :
    provenance -> namespace_table -> local_name -> absolute_name eresult **)

let lookup_function_name prov tbl ln =
  match lookup string_dec tbl.namespace_table_functions ln with
  | Some an -> esuccess (fst an) []
  | None -> function_name_not_found_error prov ln

(** val lookup_contract_name :
    provenance -> namespace_table -> local_name -> absolute_name eresult **)

let lookup_contract_name prov tbl ln =
  match lookup string_dec tbl.namespace_table_contracts ln with
  | Some an -> esuccess (fst an) []
  | None -> contract_name_not_found_error prov ln

(** val add_type_to_namespace_table :
    local_name -> absolute_name -> enum_flag -> namespace_table ->
    namespace_table **)

let add_type_to_namespace_table ln an ef tbl =
  { namespace_table_types = ((ln, (an, ef)) :: tbl.namespace_table_types);
    namespace_table_constants = tbl.namespace_table_constants;
    namespace_table_functions = tbl.namespace_table_functions;
    namespace_table_contracts = tbl.namespace_table_contracts }

(** val add_constant_to_namespace_table :
    local_name -> absolute_name -> enum_flag -> namespace_table ->
    namespace_table **)

let add_constant_to_namespace_table ln an ef tbl =
  { namespace_table_types = tbl.namespace_table_types;
    namespace_table_constants = ((ln, (an,
    ef)) :: tbl.namespace_table_constants); namespace_table_functions =
    tbl.namespace_table_functions; namespace_table_contracts =
    tbl.namespace_table_contracts }

(** val add_constants_to_namespace_table :
    (local_name * (absolute_name * enum_flag)) list -> namespace_table ->
    namespace_table **)

let add_constants_to_namespace_table lns tbl =
  { namespace_table_types = tbl.namespace_table_types;
    namespace_table_constants = (app lns tbl.namespace_table_constants);
    namespace_table_functions = tbl.namespace_table_functions;
    namespace_table_contracts = tbl.namespace_table_contracts }

(** val hide_constant_from_namespace_table :
    local_name -> namespace_table -> namespace_table **)

let hide_constant_from_namespace_table ln tbl =
  { namespace_table_types = tbl.namespace_table_types;
    namespace_table_constants =
    (filter (fun xy -> if string_dec ln (fst xy) then false else true)
      tbl.namespace_table_constants); namespace_table_functions =
    tbl.namespace_table_functions; namespace_table_contracts =
    tbl.namespace_table_contracts }

(** val add_function_to_namespace_table :
    local_name -> absolute_name -> namespace_table -> namespace_table **)

let add_function_to_namespace_table ln an tbl =
  { namespace_table_types = tbl.namespace_table_types;
    namespace_table_constants = tbl.namespace_table_constants;
    namespace_table_functions = ((ln, (an,
    EnumNone)) :: tbl.namespace_table_functions); namespace_table_contracts =
    tbl.namespace_table_contracts }

(** val add_contract_to_namespace_table :
    local_name -> absolute_name -> namespace_table -> namespace_table **)

let add_contract_to_namespace_table ln an tbl =
  { namespace_table_types = tbl.namespace_table_types;
    namespace_table_constants = tbl.namespace_table_constants;
    namespace_table_functions = tbl.namespace_table_functions;
    namespace_table_contracts = ((ln, (an,
    EnumNone)) :: tbl.namespace_table_contracts) }

type abstract_ctxt = char list list

type namespace_ctxt = { namespace_ctxt_modules : (namespace_name * namespace_table)
                                                 list;
                        namespace_ctxt_namespace : namespace_name;
                        namespace_ctxt_current_module : namespace_table;
                        namespace_ctxt_current_in_scope : namespace_table;
                        namespace_ctxt_abstract : abstract_ctxt }

(** val empty_namespace_ctxt : namespace_name -> namespace_ctxt **)

let empty_namespace_ctxt ns =
  { namespace_ctxt_modules = []; namespace_ctxt_namespace = ns;
    namespace_ctxt_current_module = empty_namespace_table;
    namespace_ctxt_current_in_scope = empty_namespace_table;
    namespace_ctxt_abstract = [] }

(** val update_namespace_context_modules :
    namespace_ctxt -> namespace_name -> (namespace_table -> namespace_table)
    -> namespace_ctxt **)

let update_namespace_context_modules ctxt ns update =
  match lookup string_dec ctxt.namespace_ctxt_modules ns with
  | Some t ->
    { namespace_ctxt_modules =
      (update_first string_dec ctxt.namespace_ctxt_modules ns (update t));
      namespace_ctxt_namespace = ctxt.namespace_ctxt_namespace;
      namespace_ctxt_current_module = ctxt.namespace_ctxt_current_module;
      namespace_ctxt_current_in_scope = ctxt.namespace_ctxt_current_in_scope;
      namespace_ctxt_abstract = ctxt.namespace_ctxt_abstract }
  | None ->
    { namespace_ctxt_modules = ((ns,
      (update empty_namespace_table)) :: ctxt.namespace_ctxt_modules);
      namespace_ctxt_namespace = ctxt.namespace_ctxt_namespace;
      namespace_ctxt_current_module = ctxt.namespace_ctxt_current_module;
      namespace_ctxt_current_in_scope = ctxt.namespace_ctxt_current_in_scope;
      namespace_ctxt_abstract = ctxt.namespace_ctxt_abstract }

(** val update_namespace_context_current_both :
    namespace_ctxt -> (namespace_table -> namespace_table) -> namespace_ctxt **)

let update_namespace_context_current_both ctxt update =
  { namespace_ctxt_modules = ctxt.namespace_ctxt_modules;
    namespace_ctxt_namespace = ctxt.namespace_ctxt_namespace;
    namespace_ctxt_current_module =
    (update ctxt.namespace_ctxt_current_module);
    namespace_ctxt_current_in_scope =
    (update ctxt.namespace_ctxt_current_in_scope); namespace_ctxt_abstract =
    ctxt.namespace_ctxt_abstract }

(** val update_namespace_context_abstract :
    namespace_ctxt -> abstract_ctxt -> namespace_ctxt **)

let update_namespace_context_abstract ctxt actxt =
  { namespace_ctxt_modules = ctxt.namespace_ctxt_modules;
    namespace_ctxt_namespace = ctxt.namespace_ctxt_namespace;
    namespace_ctxt_current_module = ctxt.namespace_ctxt_current_module;
    namespace_ctxt_current_in_scope = ctxt.namespace_ctxt_current_in_scope;
    namespace_ctxt_abstract = actxt }

(** val add_type_to_namespace_ctxt :
    namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
    enum_flag -> namespace_ctxt **)

let add_type_to_namespace_ctxt ctxt ns ln an ef =
  update_namespace_context_modules ctxt ns
    (add_type_to_namespace_table ln an ef)

(** val add_constant_to_namespace_ctxt :
    namespace_ctxt -> namespace_name -> local_name -> enum_flag ->
    absolute_name -> namespace_ctxt **)

let add_constant_to_namespace_ctxt ctxt ns ln ef an =
  update_namespace_context_modules ctxt ns
    (add_constant_to_namespace_table ln an ef)

(** val add_function_to_namespace_ctxt :
    namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
    namespace_ctxt **)

let add_function_to_namespace_ctxt ctxt ns ln an =
  update_namespace_context_modules ctxt ns
    (add_function_to_namespace_table ln an)

(** val add_contract_to_namespace_ctxt :
    namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
    namespace_ctxt **)

let add_contract_to_namespace_ctxt ctxt ns ln an =
  update_namespace_context_modules ctxt ns
    (add_contract_to_namespace_table ln an)

(** val add_type_to_namespace_ctxt_current :
    namespace_ctxt -> local_name -> absolute_name -> enum_flag ->
    namespace_ctxt **)

let add_type_to_namespace_ctxt_current ctxt ln an ef =
  update_namespace_context_current_both ctxt
    (add_type_to_namespace_table ln an ef)

(** val add_constant_to_namespace_ctxt_current :
    namespace_ctxt -> local_name -> absolute_name -> enum_flag ->
    namespace_ctxt **)

let add_constant_to_namespace_ctxt_current ctxt ln an ef =
  update_namespace_context_current_both ctxt
    (add_constant_to_namespace_table ln an ef)

(** val add_econstants_to_namespace_ctxt_current :
    namespace_ctxt -> namespace_name ->
    (local_name * (absolute_name * enum_flag)) list -> namespace_ctxt **)

let add_econstants_to_namespace_ctxt_current ctxt ens lns =
  let ctxt0 =
    fold_left (fun ctxt0 xyz ->
      let (ln, y) = xyz in
      let (an, ef) = y in
      update_namespace_context_current_both ctxt0
        (add_constant_to_namespace_table ln an ef)) lns ctxt
  in
  update_namespace_context_modules ctxt0 ens
    (add_constants_to_namespace_table lns)

(** val hide_constant_from_namespace_ctxt_current :
    namespace_ctxt -> local_name -> namespace_ctxt **)

let hide_constant_from_namespace_ctxt_current ctxt ln =
  update_namespace_context_current_both ctxt
    (hide_constant_from_namespace_table ln)

(** val hide_constants_from_namespace_ctxt_current :
    namespace_ctxt -> local_name list -> namespace_ctxt **)

let hide_constants_from_namespace_ctxt_current ctxt lns =
  fold_left hide_constant_from_namespace_ctxt_current lns ctxt

(** val add_function_to_namespace_ctxt_current :
    namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt **)

let add_function_to_namespace_ctxt_current ctxt ln an =
  update_namespace_context_current_both ctxt
    (add_function_to_namespace_table ln an)

(** val add_contract_to_namespace_ctxt_current :
    namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt **)

let add_contract_to_namespace_ctxt_current ctxt ln an =
  update_namespace_context_current_both ctxt
    (add_contract_to_namespace_table ln an)

(** val new_namespace_scope :
    namespace_ctxt -> namespace_name -> namespace_ctxt **)

let new_namespace_scope ctxt ns =
  let prev_ns = ctxt.namespace_ctxt_namespace in
  let prev_tbl_current_module = ctxt.namespace_ctxt_current_module in
  let prev_modules = ctxt.namespace_ctxt_modules in
  let prev_abstract = ctxt.namespace_ctxt_abstract in
  if string_dec prev_ns no_namespace
  then { namespace_ctxt_modules = prev_modules; namespace_ctxt_namespace =
         ns; namespace_ctxt_current_module = empty_namespace_table;
         namespace_ctxt_current_in_scope = empty_namespace_table;
         namespace_ctxt_abstract = prev_abstract }
  else (match lookup string_dec prev_modules prev_ns with
        | Some t ->
          { namespace_ctxt_modules =
            (update_first string_dec prev_modules prev_ns
              (namespace_table_app prev_tbl_current_module t));
            namespace_ctxt_namespace = ns; namespace_ctxt_current_module =
            empty_namespace_table; namespace_ctxt_current_in_scope =
            empty_namespace_table; namespace_ctxt_abstract = prev_abstract }
        | None ->
          { namespace_ctxt_modules = ((prev_ns,
            prev_tbl_current_module) :: prev_modules);
            namespace_ctxt_namespace = ns; namespace_ctxt_current_module =
            empty_namespace_table; namespace_ctxt_current_in_scope =
            empty_namespace_table; namespace_ctxt_abstract = prev_abstract })

(** val local_namespace_scope :
    namespace_ctxt -> namespace_name -> namespace_ctxt **)

let local_namespace_scope ctxt ns =
  let prev_tbl_current_module = ctxt.namespace_ctxt_current_module in
  let prev_tbl_current_in_scope = ctxt.namespace_ctxt_current_in_scope in
  let prev_modules = ctxt.namespace_ctxt_modules in
  let prev_abstract = ctxt.namespace_ctxt_abstract in
  { namespace_ctxt_modules = prev_modules; namespace_ctxt_namespace = ns;
  namespace_ctxt_current_module = prev_tbl_current_module;
  namespace_ctxt_current_in_scope = prev_tbl_current_in_scope;
  namespace_ctxt_abstract = prev_abstract }

(** val verify_name :
    (provenance -> namespace_table -> local_name -> 'a1 eresult) ->
    provenance -> namespace_ctxt -> namespace_name -> local_name -> 'a1
    eresult **)

let verify_name f_lookup prov ctxt ns ln =
  let current_ns = ctxt.namespace_ctxt_namespace in
  let current_tbl = ctxt.namespace_ctxt_current_in_scope in
  let all_modules = (current_ns, current_tbl) :: ctxt.namespace_ctxt_modules
  in
  (match lookup string_dec all_modules ns with
   | Some tbl -> f_lookup prov tbl ln
   | None -> namespace_not_found_error prov ns)

(** val verify_type_name :
    provenance -> namespace_ctxt -> namespace_name -> local_name ->
    absolute_name eresult **)

let verify_type_name prov ctxt ns ln =
  verify_name lookup_type_name prov ctxt ns ln

(** val verify_constant_name :
    provenance -> namespace_ctxt -> namespace_name -> local_name ->
    absolute_name eresult **)

let verify_constant_name prov ctxt ns ln =
  verify_name lookup_constant_name prov ctxt ns ln

(** val verify_econstant_name :
    provenance -> namespace_ctxt -> namespace_name -> local_name ->
    (absolute_name * data) eresult **)

let verify_econstant_name prov ctxt ns ln =
  verify_name lookup_econstant_name prov ctxt ns ln

(** val verify_function_name :
    provenance -> namespace_ctxt -> namespace_name -> local_name ->
    absolute_name eresult **)

let verify_function_name prov ctxt ns ln =
  verify_name lookup_function_name prov ctxt ns ln

(** val verify_contract_name :
    provenance -> namespace_ctxt -> namespace_name -> local_name ->
    absolute_name eresult **)

let verify_contract_name prov ctxt ns ln =
  verify_name lookup_contract_name prov ctxt ns ln

(** val resolve_type_name :
    provenance -> namespace_ctxt -> relative_name -> absolute_name eresult **)

let resolve_type_name prov ctxt rn =
  let tbl = ctxt.namespace_ctxt_current_in_scope in
  (match fst rn with
   | Some ns -> verify_type_name prov ctxt ns (snd rn)
   | None -> lookup_type_name prov tbl (snd rn))

(** val resolve_constant_name :
    provenance -> namespace_ctxt -> relative_name -> absolute_name eresult **)

let resolve_constant_name prov ctxt rn =
  let tbl = ctxt.namespace_ctxt_current_in_scope in
  (match fst rn with
   | Some ns -> verify_constant_name prov ctxt ns (snd rn)
   | None -> lookup_constant_name prov tbl (snd rn))

(** val resolve_econstant_name :
    provenance -> namespace_ctxt -> relative_name -> (absolute_name * data)
    eresult **)

let resolve_econstant_name prov ctxt rn =
  let tbl = ctxt.namespace_ctxt_current_in_scope in
  (match fst rn with
   | Some ns -> verify_econstant_name prov ctxt ns (snd rn)
   | None -> lookup_econstant_name prov tbl (snd rn))

(** val resolve_all_constant_name :
    provenance -> namespace_ctxt -> relative_name -> absolute_name eresult **)

let resolve_all_constant_name prov ctxt rn =
  elift_fail (fun _ -> elift fst (resolve_econstant_name prov ctxt rn))
    (resolve_constant_name prov ctxt rn)

(** val resolve_function_name :
    provenance -> namespace_ctxt -> relative_name -> absolute_name eresult **)

let resolve_function_name prov ctxt rn =
  let tbl = ctxt.namespace_ctxt_current_in_scope in
  (match fst rn with
   | Some ns -> verify_function_name prov ctxt ns (snd rn)
   | None -> lookup_function_name prov tbl (snd rn))

(** val resolve_contract_name :
    provenance -> namespace_ctxt -> relative_name -> absolute_name eresult **)

let resolve_contract_name prov ctxt rn =
  let tbl = ctxt.namespace_ctxt_current_in_scope in
  (match fst rn with
   | Some ns -> verify_contract_name prov ctxt ns (snd rn)
   | None -> lookup_contract_name prov tbl (snd rn))
