open Assoc
open Datatypes
open Ergo
open ErgoC
open ErgoCStdlib
open ErgoCSugar
open ErgoCompContext
open ErgoMap
open ErgoType
open List0
open Names
open Provenance
open QLib
open Result0
open String0
open TBrandModel
open UnaryOperators

type ergo_expr = laergo_expr

val ergo_map_expr_sane :
  brand_model -> compilation_context -> (compilation_context -> (provenance,
  provenance, absolute_name) Ergo.ergo_expr -> (provenance, provenance,
  absolute_name) Ergo.ergo_expr eresult option) -> (provenance, provenance,
  absolute_name) Ergo.ergo_expr -> (provenance, provenance, absolute_name)
  Ergo.ergo_expr eresult

val ergo_letify_function' :
  provenance -> ergo_expr -> ((char list * laergo_type option) * ergo_expr)
  list -> ergo_expr

val keep_param_types :
  (char list * laergo_type) list -> (char list * laergo_type option) list

val discard_param_types :
  (char list * laergo_type) list -> (char list * laergo_type option) list

val ergo_letify_function :
  provenance -> char list -> ergoc_function -> ergo_expr list -> ergo_expr
  eresult

val ergo_inline_functions' :
  brand_model -> compilation_context -> ergo_expr -> ergo_expr eresult option

val ergo_inline_functions :
  brand_model -> compilation_context -> (provenance, provenance,
  absolute_name) Ergo.ergo_expr -> (provenance, provenance, absolute_name)
  Ergo.ergo_expr eresult

val ergo_inline_globals' :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult
  option

val ergo_inline_globals :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult

val ergo_inline_expr :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult

val ergo_inline_function :
  brand_model -> compilation_context -> ergoc_function -> ergoc_function
  eresult

val ergoc_inline_clause :
  brand_model -> char list -> compilation_context ->
  (char list * ergoc_function) ->
  ((char list * ergoc_function) * compilation_context) eresult

val ergo_inline_contract :
  brand_model -> char list -> compilation_context -> ergoc_contract ->
  (ergoc_contract * compilation_context) eresult

val ergoc_inline_declaration :
  brand_model -> compilation_context -> ergoc_declaration ->
  (ergoc_declaration * compilation_context) eresult

val ergoc_inline_declarations :
  brand_model -> compilation_context -> ergoc_declaration list ->
  (ergoc_declaration list * compilation_context) eresult

val ergoc_inline_module :
  brand_model -> compilation_context -> ergoc_module ->
  (ergoc_module * compilation_context) eresult
