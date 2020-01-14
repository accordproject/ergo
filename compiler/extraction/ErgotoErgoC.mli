open BinaryOperators
open Data
open Datatypes
open Ergo
open ErgoC
open ErgoCSugar
open ErgoCompContext
open ErgoType
open List0
open Names
open Provenance
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators

val ergo_expr_to_ergoc_expr :
  brand_model -> compilation_context -> laergo_expr -> ergoc_expr eresult

val ergo_stmt_to_expr :
  brand_model -> compilation_context -> laergo_stmt -> ergoc_expr eresult

val clause_to_calculus :
  brand_model -> compilation_context -> laergo_type -> laergo_type option ->
  laergo_clause -> (local_name * ergoc_function) eresult

val function_to_calculus :
  brand_model -> compilation_context -> laergo_function -> ergoc_function
  eresult

val contract_to_calculus :
  brand_model -> compilation_context -> laergo_contract -> ergoc_contract
  eresult

val ergo_stmt_to_expr_top :
  brand_model -> compilation_context -> provenance -> (provenance,
  provenance, absolute_name) ergo_stmt -> ergoc_expr eresult

val declaration_to_calculus :
  brand_model -> compilation_context -> laergo_declaration ->
  (ergoc_declaration list * compilation_context) eresult

val declarations_calculus :
  brand_model -> compilation_context -> (provenance, provenance,
  absolute_name) ergo_declaration list -> (ergoc_declaration
  list * compilation_context) eresult

val ergo_module_to_calculus :
  brand_model -> compilation_context -> laergo_module ->
  (ergoc_module * compilation_context) eresult
