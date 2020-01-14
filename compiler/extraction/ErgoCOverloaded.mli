open Ast
open BinaryOperators
open Data
open DateTimeComponent
open Ergo
open ErgoCT
open MonetaryAmountComponent
open Names
open NamespaceContext
open Provenance
open QcertData
open QcertType
open QcertTypeUtil
open QcertTyping
open RType
open Result0
open TBrandModel
open UnaryOperators

type unary_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type
  eresult) * (provenance -> QLib.qcert_type -> ergoct_expr -> ergoct_expr)

type unary_dispatch_table = unary_dispatch_spec list

val make_unary_operator_fun :
  brand_model -> QLib.QcertOps.Unary.op -> provenance -> QLib.qcert_type ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_unary_operator : brand_model -> unary_op -> unary_dispatch_spec

val make_nat_minus_fun :
  brand_model -> provenance -> QLib.QcertType.qtype ->
  (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_nat_minus_criteria :
  brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
  QLib.qcert_type eresult

val make_nat_minus_operator : brand_model -> unary_dispatch_spec

val make_dot_criteria :
  brand_model -> char list -> namespace_ctxt -> provenance ->
  QLib.QcertType.qtype -> QLib.qcert_type eresult

val make_dot_operator : brand_model -> char list -> unary_dispatch_spec

val make_unbrand_dot_fun :
  brand_model -> char list -> provenance -> QLib.qcert_type ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_unbrand_dot_criteria :
  brand_model -> char list -> namespace_ctxt -> provenance ->
  QLib.QcertType.qtype -> QLib.qcert_type eresult

val make_unbrand_dot_operator :
  brand_model -> char list -> unary_dispatch_spec

val unary_operator_dispatch_table :
  brand_model -> ergo_unary_operator -> unary_dispatch_table

val try_unary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> eerror ->
  ergo_unary_operator -> unary_dispatch_table -> ergoct_expr -> ergoct_expr
  eresult

val unary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_unary_operator ->
  ergoct_expr -> ergoct_expr eresult

type binary_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type ->
  QLib.qcert_type eresult) * (provenance -> QLib.qcert_type -> ergoct_expr ->
  ergoct_expr -> ergoct_expr)

type binary_dispatch_table = binary_dispatch_spec list

val make_binary_operator_fun :
  brand_model -> QLib.QcertOps.Binary.op -> provenance -> QLib.qcert_type ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_binary_operator : brand_model -> binary_op -> binary_dispatch_spec

val make_neg_binary_operator_fun :
  brand_model -> QLib.QcertOps.Binary.op -> provenance -> QLib.qcert_type ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_neg_binary_operator :
  brand_model -> binary_op -> binary_dispatch_spec

val binary_operator_dispatch_table :
  brand_model -> ergo_binary_operator -> binary_dispatch_table

val try_binary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
  binary_dispatch_table -> ergoct_expr -> ergoct_expr -> ergoct_expr eresult

val binary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
  ergoct_expr -> ergoct_expr -> ergoct_expr eresult

type as_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type
  eresult) * (provenance -> QLib.qcert_type -> ergoct_expr -> ergoct_expr)

type as_dispatch_table = as_dispatch_spec list

val make_as_double_criteria :
  brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
  QLib.qcert_type eresult

val make_as_double_fun :
  brand_model -> char list -> provenance -> QLib.QcertType.qtype ->
  (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_as_double : brand_model -> char list -> as_dispatch_spec

val make_as_datetime_criteria :
  brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
  QLib.qcert_type eresult

val make_as_datetime_fun :
  brand_model -> char list -> provenance -> QLib.QcertType.qtype ->
  (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_as_datetime : brand_model -> char list -> as_dispatch_spec

val make_as_monetaryamount_criteria :
  brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
  QLib.qcert_type eresult

val make_as_monetaryamount_fun :
  brand_model -> char list -> provenance -> QLib.qcert_type ->
  (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_as_monetaryamount : brand_model -> char list -> as_dispatch_spec

val as_operator_dispatch_table : brand_model -> char list -> as_dispatch_table

val try_as_dispatch :
  brand_model -> namespace_ctxt -> provenance -> eerror -> char list ->
  as_dispatch_table -> ergoct_expr -> ergoct_expr eresult

val as_dispatch :
  brand_model -> namespace_ctxt -> provenance -> char list -> ergoct_expr ->
  ergoct_expr eresult
