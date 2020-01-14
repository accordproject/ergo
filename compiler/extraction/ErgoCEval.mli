open Assoc
open Ast
open BinaryOperators
open Bindings
open BrandRelation
open Data
open Datatypes
open Ergo
open ErgoCEvalContext
open ErgoCT
open List0
open Provenance
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators

val ergo_unary_builtin_eval :
  brand_model -> provenance -> unary_op -> QLib.qcert_data -> QLib.qcert_data
  eresult

val ergo_binary_builtin_eval :
  brand_model -> provenance -> binary_op -> QLib.qcert_data ->
  QLib.qcert_data -> QLib.qcert_data eresult

val ergoct_eval_expr :
  brand_model -> eval_context -> ergoct_expr -> QLib.qcert_data eresult

val ergoct_eval_decl :
  brand_model -> eval_context -> ergoct_declaration ->
  (eval_context * QLib.qcert_data option) eresult
