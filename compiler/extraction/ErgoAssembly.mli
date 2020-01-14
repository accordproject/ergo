open Datatypes
open Ergo
open ErgoType
open List0
open Names
open Provenance
open Result0
open String0

val toDraftClause : provenance -> char list -> laergo_expr -> laergo_clause

val add_template_to_clauses :
  provenance -> (char list * laergo_expr) list -> laergo_clause list ->
  laergo_clause list

val add_template_to_contract :
  (char list * laergo_expr) list -> laergo_contract -> (provenance,
  provenance, absolute_name) ergo_contract

val add_template_to_declaration :
  (char list * laergo_expr) list -> laergo_declaration -> laergo_declaration

val add_template_to_module :
  (char list * laergo_expr) list -> laergo_module -> (provenance, provenance,
  absolute_name) ergo_module

val template_of_ergo_declaration :
  laergo_declaration -> (char list * char list) list

val template_of_ergo_declarations :
  laergo_declaration list -> (char list * char list) list

val template_of_ergo_module : laergo_module -> (char list * char list) list

val template_of_ergo_modules :
  laergo_module list -> (char list * char list) list

val find_template : provenance -> laergo_module list -> laergo_type eresult

val empty_main :
  provenance -> char list -> laergo_module list -> laergo_module eresult
