open BrandRelation
open CompDriver
open Datatypes
open EmitUtil
open ErgoImp
open ErgoType
open JavaScriptAst
open List0
open Names
open NativeString
open Provenance
open QLib
open String0
open TBrandModel
open Version

val accord_annotation :
  bool -> char list -> char list -> char list -> char list -> char list ->
  nstring -> nstring -> nstring

val ergo_imp_function_to_javascript_ast :
  brand_model -> char list -> ergo_imp_lambda -> char list option -> js_ast

val ergo_imp_function_table_to_javascript_ast :
  brand_model -> char list -> ergo_imp_function_table -> js_ast

val preamble : js_ast

val postamble : js_ast

val ergo_imp_declaration_to_javascript_ast :
  brand_model -> ergo_imp_declaration -> js_ast

val ergo_imp_declarations_to_javascript_ast :
  brand_model -> ergo_imp_declaration list -> js_ast

val ergo_imp_module_to_javascript_ast :
  brand_model -> ergo_imp_module -> topdecl list

val ergo_imp_module_to_javascript_top :
  brand_model -> (char list * char list) list -> ergo_imp_module ->
  QcertCodeGen.ejavascript

val wrapper_function_for_clause :
  bool -> char list -> char list -> char list -> char list -> char list ->
  char list -> char list -> char list -> nstring -> nstring -> nstring

val apply_wrapper_function :
  char list -> char list ->
  ((((char list * char list) * char list) * char list) * char list) ->
  nstring -> nstring -> nstring

val wrapper_functions :
  char list ->
  (((((char list * char list) * char list) * char list) * char list)
  list * char list) -> nstring -> nstring -> nstring

val javascript_of_module_with_dispatch :
  brand_model -> char list ->
  (((((char list * char list) * char list) * char list) * char list)
  list * char list) -> ergo_imp_module -> nstring -> nstring -> nstring

val filter_signatures :
  char list -> (char list * laergo_type_signature) list ->
  ((((char list * char list) * char list) * char list) * char list) list

val filter_signatures_with_state :
  char list -> laergo_type option -> (char list * (provenance, absolute_name)
  ergo_type_signature) list ->
  ((((char list * char list) * char list) * char list) * char list)
  list * char list

val ergo_imp_module_to_es6 :
  brand_model -> char list -> (provenance, absolute_name) ergo_type option ->
  (char list * (provenance, absolute_name) ergo_type_signature) list ->
  ergo_imp_module -> QcertCodeGen.ejavascript
