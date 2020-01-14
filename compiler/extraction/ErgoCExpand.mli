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

val create_call :
  provenance -> char list -> char list -> char list -> ergoc_expr ->
  ergoc_expr list -> (char list * laergo_type) list -> ergoc_expr eresult

val case_of_sig :
  provenance -> char list -> char list -> ergoc_expr -> ergoc_expr list ->
  (char list * sigc) -> (absolute_name * ((provenance, absolute_name)
  ergo_pattern * ergoc_expr)) list eresult

val make_cases :
  laergo_type_declaration list -> provenance ->
  (absolute_name * (laergo_pattern * ergoc_expr)) list ->
  (laergo_pattern * ergoc_expr) list eresult

val match_of_sigs :
  laergo_type_declaration list -> provenance -> char list -> char list ->
  ergoc_expr -> ergoc_expr list -> (char list * sigc) list -> ergoc_expr
  eresult

val match_of_sigs_top :
  laergo_type_declaration list -> provenance -> char list -> ergoc_expr list
  -> (char list * sigc) list -> ergoc_expr eresult

val filter_init : (char list * sigc) list -> (char list * sigc) list

val create_main_clause_for_contract :
  laergo_type_declaration list -> provenance -> char list -> ergoc_contract
  -> (local_name * ergoc_function) eresult

val default_state : provenance -> ergoc_expr

val create_init_clause_for_contract :
  provenance -> ergoc_contract -> local_name * ergoc_function

val add_init_clause_to_contract : ergoc_contract -> ergoc_contract

val add_main_clause_to_contract :
  laergo_type_declaration list -> char list -> ergoc_contract ->
  ergoc_contract eresult

val ergoc_expand_declaration :
  laergo_type_declaration list -> ergoc_declaration -> ergoc_declaration
  eresult

val ergoc_expand_declarations :
  laergo_type_declaration list -> ergoc_declaration list -> ergoc_declaration
  list eresult

val ergoc_expand_module :
  laergo_type_declaration list -> ergoc_module -> ergoc_module eresult
