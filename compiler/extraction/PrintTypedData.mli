open Ascii
open CoqLibAdd
open Data
open Datatypes
open Lift
open List0
open Misc
open Names
open NamespaceContext
open Provenance
open QcertData
open QcertType
open RType
open Result0
open String0
open StringAdd
open TBrandModel
open ToString
open UnaryOperators
open UnaryOperatorsSem

val print_brand : namespace_ctxt -> char list -> char list

val print_multiple_brands : namespace_ctxt -> char list list -> char list

val unpack_output :
  QLib.qcert_data -> ((QLib.qcert_data * QLib.qcert_data
  list) * QLib.qcert_data) option

val fmt_nl : char list

val string_of_enum : namespace_ctxt -> QLib.qcert_data -> char list

val string_of_data : namespace_ctxt -> QLib.qcert_data -> char list

val rtype_to_string : namespace_ctxt -> rtype_UU2080_ -> char list

val qcert_type_to_string :
  brand_model -> namespace_ctxt -> QLib.qcert_type -> char list

val string_of_result_type :
  brand_model -> namespace_ctxt -> QLib.qcert_type option -> char list

val unpack_error :
  brand_model -> namespace_ctxt -> char list -> QLib.qcert_type -> eerror

val unpack_failure_type :
  brand_model -> namespace_ctxt -> QLib.qcert_type -> QLib.qcert_type eresult

val unpack_success_type :
  brand_model -> namespace_ctxt -> QLib.qcert_type -> ewarning list ->
  ((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) eresult

val unpack_output_type :
  brand_model -> namespace_ctxt -> QLib.qcert_type -> ewarning list ->
  (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
  eresult

val string_of_response :
  brand_model -> namespace_ctxt -> QLib.qcert_data -> QLib.qcert_type option
  -> char list

val string_of_emits :
  brand_model -> namespace_ctxt -> QLib.qcert_data list -> QLib.qcert_type
  option -> char list

val string_of_state :
  brand_model -> namespace_ctxt -> QLib.qcert_data option -> QLib.qcert_data
  -> QLib.qcert_type option -> char list

val string_of_typed_data :
  brand_model -> namespace_ctxt -> QLib.qcert_data option -> QLib.qcert_data
  -> QLib.qcert_type option -> char list

val string_of_typed_result :
  brand_model -> namespace_ctxt -> QLib.qcert_data option -> (QLib.qcert_type
  option * QLib.qcert_data option) -> char list
