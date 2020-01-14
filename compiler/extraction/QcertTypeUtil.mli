open Ast
open BinaryOperators
open NamespaceContext
open PrintTypedData
open Provenance
open QcertType
open RType
open Result0
open String0
open TBrandModel
open UnaryOperators

val empty_rec_type : brand_model -> QLib.qcert_type

val ergo_format_unop_error :
  brand_model -> namespace_ctxt -> unary_op -> QLib.qcert_type -> char list

val ergo_format_binop_error :
  brand_model -> namespace_ctxt -> binary_op -> QLib.qcert_type ->
  QLib.qcert_type -> char list

val ergo_format_as_operator_dispatch_error :
  brand_model -> namespace_ctxt -> QLib.qcert_type -> char list

val ergo_format_unary_operator_dispatch_error :
  brand_model -> namespace_ctxt -> ergo_unary_operator -> QLib.qcert_type ->
  char list

val ergo_format_binary_operator_dispatch_error :
  brand_model -> namespace_ctxt -> ergo_binary_operator -> QLib.qcert_type ->
  QLib.qcert_type -> char list

val ergo_format_new_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type -> char list

val ergo_format_clause_return_fallback_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
  QLib.qcert_type -> char list

val ergo_format_clause_return_component_error :
  brand_model -> namespace_ctxt -> char list -> char list -> char list ->
  QLib.qcert_type -> QLib.qcert_type -> char list

val ergo_format_clause_return_normal_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
  QLib.qcert_type ->
  (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
  ->
  (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
  -> char list

val ergo_format_clause_return_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
  QLib.qcert_type -> char list

val ergo_format_function_return_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
  QLib.qcert_type -> char list

val make_unary_operator_criteria :
  brand_model -> unary_op -> namespace_ctxt -> provenance ->
  QLib.QcertType.qtype -> QLib.qcert_type eresult

val make_binary_operator_criteria :
  brand_model -> binary_op -> namespace_ctxt -> provenance ->
  QLib.QcertType.qtype -> QLib.QcertType.qtype -> QLib.qcert_type eresult
