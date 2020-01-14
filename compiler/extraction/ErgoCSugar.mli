open BinaryOperators
open BrandRelation
open Data
open Ergo
open ErgoC
open ErgoType
open Lift
open Names
open Provenance
open String0
open UnaryOperators

val mkResult :
  provenance -> (provenance, provenance, absolute_name) ergo_expr ->
  (provenance, provenance, absolute_name) ergo_expr -> (provenance,
  provenance, absolute_name) ergo_expr -> ergoc_expr

val setState :
  provenance -> (provenance, provenance, absolute_name) ergo_expr ->
  (provenance, provenance, absolute_name) ergo_expr -> ergoc_expr

val thisThis : provenance -> ergoc_expr

val setStateDot :
  provenance -> char list -> brand -> (provenance, provenance, char list)
  ergo_expr -> (provenance, provenance, absolute_name) ergo_expr -> ergoc_expr

val thisContract : provenance -> ergoc_expr

val thisClause : provenance -> char list -> ergoc_expr

val thisState : provenance -> ergoc_expr

val pushEmit :
  provenance -> (provenance, provenance, char list) ergo_expr -> (provenance,
  provenance, char list) ergo_expr -> ergoc_expr

val coq_ESuccess : provenance -> ergoc_expr -> ergoc_expr

val coq_EFailure : provenance -> ergoc_expr -> ergoc_expr

val coq_ECallClause :
  provenance -> char list -> char list -> ergoc_expr list -> ergoc_expr

val coq_EReturn : provenance -> ergoc_expr -> ergoc_expr

val coq_EBindThis :
  provenance -> char list -> ergoc_expr -> (provenance, provenance,
  absolute_name) ergo_expr

val coq_EWrapTop :
  provenance -> ergoc_expr -> (provenance, provenance, char list) ergo_expr

val coq_EClauseAsFunction :
  provenance -> char list -> laergo_type -> laergo_type option -> laergo_type
  option -> laergo_type option -> (char list * (provenance, absolute_name)
  ergo_type) list -> ergoc_expr option -> char list * ergoc_function
