open Assoc
open Ast
open Basics
open BinaryOperators
open Datatypes
open Ergo
open ErgoC
open ErgoCOverloaded
open ErgoCT
open ErgoCTypecheckContext
open ErgoTypetoQcertType
open List0
open Names
open NamespaceContext
open PrintTypedData
open Provenance
open QcertData
open QcertDataTyping
open QcertType
open QcertTypeUtil
open RSubtype
open Result0
open String0
open TBrandModel
open TDataInfer
open UnaryOperators

val ergoc_expr_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_expr -> ergoct_expr
  eresult

val ergoc_function_typecheck :
  brand_model -> namespace_ctxt -> char list -> type_context ->
  ergoc_function -> (ergoct_function * type_context) eresult

val ergoc_clause_typecheck :
  brand_model -> namespace_ctxt -> type_context ->
  (char list * ergoc_function) ->
  ((char list * ergoct_function) * type_context) eresult

val ergoc_contract_typecheck :
  brand_model -> namespace_ctxt -> type_context -> absolute_name ->
  ergoc_contract -> (ergoct_contract * type_context) eresult

val ergoc_decl_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_declaration ->
  (ergoct_declaration * type_context) eresult

val ergoc_module_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_module ->
  (ergoct_module * type_context) eresult
