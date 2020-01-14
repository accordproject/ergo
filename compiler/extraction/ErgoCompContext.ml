open Assoc
open Datatypes
open ErgoC
open ErgoCTypecheckContext
open ErgoNameResolve
open ErgoType
open Lift
open List0
open Names
open NamespaceContext
open Result0
open String0
open TBrandModel

type function_group_env =
  (char list * (char list * ergoc_function) list) list

type compilation_context = { compilation_context_namespace : namespace_ctxt;
                             compilation_context_function_env : (char list * ergoc_function)
                                                                list;
                             compilation_context_function_group_env : 
                             function_group_env;
                             compilation_context_global_env : (char list * ergoc_expr)
                                                              list;
                             compilation_context_local_env : (char list * ergoc_expr)
                                                             list;
                             compilation_context_params_env : char list list;
                             compilation_context_current_contract : char list
                                                                    option;
                             compilation_context_current_clause : char list
                                                                  option;
                             compilation_context_type_ctxt : type_context;
                             compilation_context_type_decls : laergo_type_declaration
                                                              list;
                             compilation_context_new_type_decls : laergo_type_declaration
                                                                  list;
                             compilation_context_warnings : ewarning list;
                             compilation_context_state_type : laergo_type
                                                              option }

(** val namespace_ctxt_of_compilation_context :
    brand_model -> compilation_context -> namespace_ctxt **)

let namespace_ctxt_of_compilation_context _ ctxt =
  ctxt.compilation_context_namespace

(** val compilation_context_update_namespace :
    brand_model -> compilation_context -> namespace_ctxt ->
    compilation_context **)

let compilation_context_update_namespace _ ctxt nsctxt =
  { compilation_context_namespace = nsctxt;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_update_function_env :
    brand_model -> compilation_context -> char list -> ergoc_function ->
    compilation_context **)

let compilation_context_update_function_env _ ctxt name value =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ((name,
    value) :: ctxt.compilation_context_function_env);
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val update_function_group_env :
    char list -> char list -> ergoc_function -> function_group_env ->
    function_group_env **)

let update_function_group_env gname fname fn fg_env =
  match lookup string_dec fg_env gname with
  | Some t -> update_first string_dec fg_env gname ((fname, fn) :: t)
  | None -> (gname, ((fname, fn) :: [])) :: fg_env

(** val compilation_context_update_function_group_env :
    brand_model -> compilation_context -> char list -> char list ->
    ergoc_function -> compilation_context **)

let compilation_context_update_function_group_env _ ctxt coname clname value =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    (update_function_group_env coname clname value
      ctxt.compilation_context_function_group_env);
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_update_global_env :
    brand_model -> compilation_context -> char list -> ergoc_expr ->
    compilation_context **)

let compilation_context_update_global_env _ ctxt name value =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ((name,
    value) :: ctxt.compilation_context_global_env);
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_update_local_env :
    brand_model -> compilation_context -> char list -> ergoc_expr ->
    compilation_context **)

let compilation_context_update_local_env _ ctxt name value =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ((name,
    value) :: ctxt.compilation_context_local_env);
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_set_params_env :
    brand_model -> compilation_context -> char list list ->
    compilation_context **)

let compilation_context_set_params_env _ ctxt params =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = params;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val set_namespace_in_compilation_context :
    brand_model -> namespace_name -> compilation_context ->
    compilation_context eresult **)

let set_namespace_in_compilation_context bm ns ctxt =
  elift (compilation_context_update_namespace bm ctxt)
    (new_ergo_module_namespace
      (namespace_ctxt_of_compilation_context bm ctxt) ns)

(** val set_current_contract :
    brand_model -> compilation_context -> char list -> laergo_type option ->
    compilation_context **)

let set_current_contract _ ctxt cname tname =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract = (Some cname);
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    tname }

(** val set_current_clause :
    brand_model -> compilation_context -> char list -> compilation_context **)

let set_current_clause _ ctxt cname =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause = (Some cname);
    compilation_context_type_ctxt = ctxt.compilation_context_type_ctxt;
    compilation_context_type_decls = ctxt.compilation_context_type_decls;
    compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_update_type_ctxt :
    brand_model -> compilation_context -> type_context -> compilation_context **)

let compilation_context_update_type_ctxt _ ctxt nctxt =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    nctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_update_type_declarations :
    brand_model -> compilation_context -> laergo_type_declaration list ->
    laergo_type_declaration list -> compilation_context **)

let compilation_context_update_type_declarations _ ctxt old_decls new_decls =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    (sort_decls old_decls); compilation_context_new_type_decls =
    (sort_decls new_decls); compilation_context_warnings =
    ctxt.compilation_context_warnings; compilation_context_state_type =
    ctxt.compilation_context_state_type }

(** val compilation_context_add_new_type_declaration :
    brand_model -> compilation_context -> laergo_type_declaration ->
    compilation_context **)

let compilation_context_add_new_type_declaration _ ctxt decl =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    (sort_decls (app ctxt.compilation_context_new_type_decls (decl :: [])));
    compilation_context_warnings = ctxt.compilation_context_warnings;
    compilation_context_state_type = ctxt.compilation_context_state_type }

(** val compilation_context_add_warnings :
    brand_model -> compilation_context -> ewarning list -> compilation_context **)

let compilation_context_add_warnings _ ctxt warnings =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    (app ctxt.compilation_context_warnings warnings);
    compilation_context_state_type = ctxt.compilation_context_state_type }

(** val compilation_context_reset_warnings :
    brand_model -> compilation_context -> compilation_context **)

let compilation_context_reset_warnings _ ctxt =
  { compilation_context_namespace = ctxt.compilation_context_namespace;
    compilation_context_function_env = ctxt.compilation_context_function_env;
    compilation_context_function_group_env =
    ctxt.compilation_context_function_group_env;
    compilation_context_global_env = ctxt.compilation_context_global_env;
    compilation_context_local_env = ctxt.compilation_context_local_env;
    compilation_context_params_env = ctxt.compilation_context_params_env;
    compilation_context_current_contract =
    ctxt.compilation_context_current_contract;
    compilation_context_current_clause =
    ctxt.compilation_context_current_clause; compilation_context_type_ctxt =
    ctxt.compilation_context_type_ctxt; compilation_context_type_decls =
    ctxt.compilation_context_type_decls; compilation_context_new_type_decls =
    ctxt.compilation_context_new_type_decls; compilation_context_warnings =
    []; compilation_context_state_type = ctxt.compilation_context_state_type }

(** val get_all_decls :
    brand_model -> compilation_context -> laergo_type_declaration list **)

let get_all_decls _ ctxt =
  sort_decls
    (app ctxt.compilation_context_type_decls
      ctxt.compilation_context_new_type_decls)

(** val init_compilation_context :
    brand_model -> namespace_ctxt -> laergo_type_declaration list ->
    compilation_context **)

let init_compilation_context bm nsctxt decls =
  { compilation_context_namespace = nsctxt;
    compilation_context_function_env = [];
    compilation_context_function_group_env = [];
    compilation_context_global_env = []; compilation_context_local_env = [];
    compilation_context_params_env = [];
    compilation_context_current_contract = None;
    compilation_context_current_clause = None;
    compilation_context_type_ctxt =
    (empty_type_context bm.brand_model_relation);
    compilation_context_type_decls = decls;
    compilation_context_new_type_decls = []; compilation_context_warnings =
    []; compilation_context_state_type = None }

(** val is_abstract_class :
    brand_model -> compilation_context -> char list -> bool **)

let is_abstract_class _ ctxt n =
  if in_dec string_dec n
       ctxt.compilation_context_namespace.namespace_ctxt_abstract
  then true
  else false

(** val is_state_type_branded :
    brand_model -> compilation_context -> char list option **)

let is_state_type_branded _ ctxt =
  let t = ctxt.compilation_context_state_type in olift type_name_of_type t
