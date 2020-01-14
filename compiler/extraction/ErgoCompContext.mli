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

val namespace_ctxt_of_compilation_context :
  brand_model -> compilation_context -> namespace_ctxt

val compilation_context_update_namespace :
  brand_model -> compilation_context -> namespace_ctxt -> compilation_context

val compilation_context_update_function_env :
  brand_model -> compilation_context -> char list -> ergoc_function ->
  compilation_context

val update_function_group_env :
  char list -> char list -> ergoc_function -> function_group_env ->
  function_group_env

val compilation_context_update_function_group_env :
  brand_model -> compilation_context -> char list -> char list ->
  ergoc_function -> compilation_context

val compilation_context_update_global_env :
  brand_model -> compilation_context -> char list -> ergoc_expr ->
  compilation_context

val compilation_context_update_local_env :
  brand_model -> compilation_context -> char list -> ergoc_expr ->
  compilation_context

val compilation_context_set_params_env :
  brand_model -> compilation_context -> char list list -> compilation_context

val set_namespace_in_compilation_context :
  brand_model -> namespace_name -> compilation_context -> compilation_context
  eresult

val set_current_contract :
  brand_model -> compilation_context -> char list -> laergo_type option ->
  compilation_context

val set_current_clause :
  brand_model -> compilation_context -> char list -> compilation_context

val compilation_context_update_type_ctxt :
  brand_model -> compilation_context -> type_context -> compilation_context

val compilation_context_update_type_declarations :
  brand_model -> compilation_context -> laergo_type_declaration list ->
  laergo_type_declaration list -> compilation_context

val compilation_context_add_new_type_declaration :
  brand_model -> compilation_context -> laergo_type_declaration ->
  compilation_context

val compilation_context_add_warnings :
  brand_model -> compilation_context -> ewarning list -> compilation_context

val compilation_context_reset_warnings :
  brand_model -> compilation_context -> compilation_context

val get_all_decls :
  brand_model -> compilation_context -> laergo_type_declaration list

val init_compilation_context :
  brand_model -> namespace_ctxt -> laergo_type_declaration list ->
  compilation_context

val is_abstract_class :
  brand_model -> compilation_context -> char list -> bool

val is_state_type_branded :
  brand_model -> compilation_context -> char list option
