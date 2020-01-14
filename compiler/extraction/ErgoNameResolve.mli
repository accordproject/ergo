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

val namespace_ctxt_of_ergo_decls :
  namespace_ctxt -> namespace_name -> lrergo_declaration list ->
  namespace_name * namespace_ctxt

val namespace_ctxt_of_ergo_module :
  namespace_ctxt -> lrergo_module -> namespace_ctxt

val namespace_ctxt_of_cto_packages :
  namespace_ctxt -> (provenance, relative_name) cto_package list ->
  namespace_ctxt

val lookup_one_import :
  namespace_ctxt -> limport_decl -> namespace_table eresult

val resolve_one_import :
  namespace_ctxt -> limport_decl -> namespace_ctxt eresult

val builtin_imports : char list list

val is_builtin_import : namespace_name -> bool

val stdlib_imports : char list list

val is_stdlib_import : namespace_name -> bool

val resolve_ergo_type : namespace_ctxt -> lrergo_type -> laergo_type eresult

val resolve_ergo_type_struct :
  namespace_ctxt -> (char list * lrergo_type) list ->
  (char list * laergo_type) list eresult

val resolve_type_annotation :
  provenance -> namespace_ctxt -> relative_name option -> absolute_name
  option eresult

val resolve_extends :
  provenance -> namespace_ctxt -> rextends -> aextends eresult

val resolve_ergo_type_signature :
  provenance -> namespace_ctxt -> char list -> lrergo_type_signature ->
  laergo_type_signature eresult

val resolve_ergo_type_clauses :
  provenance -> namespace_ctxt -> (char list * lrergo_type_signature) list ->
  (char list * laergo_type_signature) list eresult

val resolve_ergo_type_declaration_desc :
  provenance -> namespace_ctxt -> char list -> lrergo_type_declaration_desc
  -> laergo_type_declaration_desc eresult

val resolve_ergo_type_declaration :
  provenance -> namespace_name -> namespace_ctxt ->
  (abstract_ctxt * lrergo_type_declaration) ->
  ((abstract_ctxt * laergo_declaration) * ((char list * laergo_expr) * data)
  list) eresult

val resolve_ergo_pattern :
  namespace_ctxt -> lrergo_pattern -> laergo_pattern eresult

val resolve_ergo_expr : namespace_ctxt -> lrergo_expr -> laergo_expr eresult

val resolve_ergo_stmt : namespace_ctxt -> lrergo_stmt -> laergo_stmt eresult

val resolve_ergo_function :
  namespace_name -> namespace_ctxt -> char list -> lrergo_function ->
  laergo_function eresult

val resolve_ergo_clause :
  namespace_name -> namespace_ctxt -> (provenance, provenance, relative_name)
  ergo_clause -> laergo_clause eresult

val resolve_ergo_clauses :
  namespace_name -> namespace_ctxt -> (provenance, provenance, relative_name)
  ergo_clause list -> laergo_clause list eresult

val resolve_ergo_contract :
  namespace_name -> namespace_ctxt -> lrergo_contract -> laergo_contract
  eresult

val resolve_ergo_declaration :
  namespace_ctxt -> lrergo_declaration -> (laergo_declaration
  list * namespace_ctxt) eresult

val resolve_ergo_template_expr :
  namespace_ctxt -> lrergo_expr -> laergo_expr eresult

val resolve_ergo_declarations :
  namespace_ctxt -> lrergo_declaration list -> ((provenance, provenance,
  absolute_name) ergo_declaration list * namespace_ctxt) eresult

val silently_resolve_ergo_declarations :
  namespace_ctxt -> lrergo_declaration list -> namespace_ctxt eresult

val init_namespace_ctxt : namespace_ctxt

val patch_cto_imports :
  namespace_name -> lrergo_declaration list -> lrergo_declaration list

val patch_ergo_imports :
  namespace_name -> lrergo_declaration list -> lrergo_declaration list

val new_ergo_module_namespace :
  namespace_ctxt -> namespace_name -> namespace_ctxt eresult

val resolve_cto_package :
  namespace_ctxt -> lrcto_package -> (laergo_module * namespace_ctxt) eresult

val resolve_ergo_module :
  namespace_ctxt -> lrergo_module -> (laergo_module * namespace_ctxt) eresult

val resolve_ergo_template :
  namespace_ctxt -> (char list * lrergo_expr) list ->
  (char list * laergo_expr) list eresult

val resolve_ergo_modules :
  namespace_ctxt -> lrergo_module list -> (laergo_module
  list * namespace_ctxt) eresult

val resolve_cto_packages :
  namespace_ctxt -> lrcto_package list -> (laergo_module
  list * namespace_ctxt) eresult

val triage_ctos_and_ergos :
  lrergo_input list -> (lrcto_package list * lrergo_module
  list) * lrergo_module option
