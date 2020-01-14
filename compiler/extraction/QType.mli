open BinaryOperators
open Bindings
open BrandRelation
open Data
open DataResult
open Datatypes
open List0
open QcertData
open QcertDataTyping
open QcertType
open QcertTyping
open RSubtype
open RType
open RTypeMeetJoin
open Schema
open String0
open TBrandContext
open TBrandModel
open TBrandModelProp
open TDataInfer
open TOperatorsInferSub
open TUtil
open UnaryOperators

module QType :
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 sig
  val empty_brand_model : unit -> brand_model

  type record_kind = RType.record_kind

  val open_kind : record_kind

  val closed_kind : record_kind

  type qtype_struct = rtype_UU2080_

  type qtype = rtype

  type t = qtype

  val tbottom : brand_relation -> qtype

  val ttop : brand_relation -> qtype

  val tunit : brand_relation -> qtype

  val tfloat : brand_relation -> qtype

  val tnat : brand_relation -> qtype

  val tbool : brand_relation -> qtype

  val tstring : brand_relation -> qtype

  val tdateTimeFormat : brand_relation -> qtype

  val tdateTime : brand_relation -> qtype

  val tduration : brand_relation -> qtype

  val tperiod : brand_relation -> qtype

  val tcoll : brand_relation -> qtype -> qtype

  val trec :
    brand_relation -> record_kind -> (char list * qtype) list -> qtype

  val teither : brand_relation -> qtype -> qtype -> qtype

  val tarrow : brand_relation -> qtype -> qtype -> qtype

  val tbrand : brand_relation -> char list list -> qtype

  val toption : brand_relation -> qtype -> qtype

  val qcert_type_meet : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_join : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_subtype_dec : brand_model -> qtype -> qtype -> bool

  val untcoll : brand_model -> qtype -> qtype option

  val unteither : brand_model -> qtype -> (qtype * qtype) option

  val untrec :
    brand_model -> qtype -> (record_kind * (char list * qtype) list) option

  val qcert_type_infer_data : brand_model -> data -> qtype option

  val qcert_type_infer_binary_op :
    brand_model -> binary_op -> qtype -> qtype -> ((qtype * qtype) * qtype)
    option

  val qcert_type_infer_unary_op :
    brand_model -> unary_op -> qtype -> (qtype * qtype) option

  val unpack_qcert_type : brand_relation -> qtype -> qtype_struct

  type tbrand_relation = brand_relation

  val tempty_brand_relation : tbrand_relation

  val mk_tbrand_relation :
    (char list * char list) list -> tbrand_relation qresult

  type tbrand_context_decls = brand_context_decls

  type tbrand_context = brand_context

  val mk_tbrand_context :
    brand_relation -> tbrand_context_decls -> tbrand_context

  type tbrand_model = brand_model

  val mk_tbrand_model :
    brand_relation -> tbrand_context_decls -> tbrand_model qresult

  val tempty_brand_model : tbrand_model

  val qcert_type_unpack : brand_relation -> qtype -> qtype_struct

  val qcert_type_closed_from_open : brand_model -> qtype -> qtype

  val infer_brand_strict :
    brand_model -> brands -> qtype -> (rtype * qtype) option

  val recminus :
    brand_relation -> (char list * rtype) list -> char list list ->
    (char list * rtype) list

  val diff_record_types :
    brand_model -> brands -> qtype -> (char list list * char list list) option

  val rec_fields_that_are_not_subtype :
    brand_model -> (char list * qtype) list -> (char list * qtype) list ->
    ((char list * qtype) * qtype) list

  val fields_that_are_not_subtype :
    brand_model -> brands -> qtype -> ((char list * qtype) * qtype) list
 end
