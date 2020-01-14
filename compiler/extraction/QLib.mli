open BinaryOperators
open BrandRelation
open CompLang
open Data
open DataResult
open DataSystem
open DateTimeComponent
open ForeignData
open ForeignType
open ForeignTyping
open ImpEJson
open JSON
open Java
open JavaScriptAst
open ListAdd
open NNRC
open NativeString
open QcertData
open QcertEJson
open QcertModel
open QcertType
open RType
open TBrandContext
open TBrandModel
open UnaryOperators
open Var
open CNNRC

module QcertBackend :
 sig
  type ergo_foreign_ejson = enhanced_ejson

  type ergo_foreign_ejson_runtime_op = enhanced_foreign_ejson_runtime_op

  val ergo_foreign_data : foreign_data

  val ergo_foreign_type : foreign_type

  module Enhanced :
   sig
    module Model :
     sig
      val basic_model : brand_model -> basic_model

      val foreign_type : foreign_type

      val foreign_typing : brand_model -> foreign_typing
     end

    module Data :
     sig
      val ddate_time : coq_DATE_TIME -> data

      val ddate_time_duration : coq_DATE_TIME_DURATION -> data

      val ddate_time_period : coq_DATE_TIME_PERIOD -> data
     end

    module Ops :
     sig
      module Unary :
       sig
        val date_time_get_seconds : unary_op

        val date_time_get_minutes : unary_op

        val date_time_get_hours : unary_op

        val date_time_get_days : unary_op

        val date_time_get_weeks : unary_op

        val date_time_get_months : unary_op

        val date_time_get_quarters : unary_op

        val date_time_get_years : unary_op

        val date_time_start_of_day : unary_op

        val date_time_start_of_week : unary_op

        val date_time_start_of_month : unary_op

        val date_time_start_of_quarter : unary_op

        val date_time_start_of_year : unary_op

        val date_time_end_of_day : unary_op

        val date_time_end_of_week : unary_op

        val date_time_end_of_month : unary_op

        val date_time_end_of_quarter : unary_op

        val date_time_end_of_year : unary_op

        val date_time_format_from_string : unary_op

        val date_time_from_string : unary_op

        val date_time_min : unary_op

        val date_time_max : unary_op

        val date_time_duration_amount : unary_op

        val date_time_duration_from_string : unary_op

        val date_time_duration_from_seconds : unary_op

        val date_time_duration_from_minutes : unary_op

        val date_time_duration_from_hours : unary_op

        val date_time_duration_from_days : unary_op

        val date_time_duration_from_weeks : unary_op

        val date_time_period_from_string : unary_op

        val date_time_period_from_days : unary_op

        val date_time_period_from_weeks : unary_op

        val date_time_period_from_months : unary_op

        val date_time_period_from_quarters : unary_op

        val date_time_period_from_years : unary_op

        val coq_OpDateTimeGetSeconds : unary_op

        val coq_OpDateTimeGetMinutes : unary_op

        val coq_OpDateTimeGetHours : unary_op

        val coq_OpDateTimeGetDays : unary_op

        val coq_OpDateTimeGetWeeks : unary_op

        val coq_OpDateTimeGetMonths : unary_op

        val coq_OpDateTimeGetQuarters : unary_op

        val coq_OpDateTimeGetYears : unary_op

        val coq_OpDateTimeStartOfDay : unary_op

        val coq_OpDateTimeStartOfWeek : unary_op

        val coq_OpDateTimeStartOfMonth : unary_op

        val coq_OpDateTimeStartOfQuarter : unary_op

        val coq_OpDateTimeStartOfYear : unary_op

        val coq_OpDateTimeEndOfDay : unary_op

        val coq_OpDateTimeEndOfWeek : unary_op

        val coq_OpDateTimeEndOfMonth : unary_op

        val coq_OpDateTimeEndOfQuarter : unary_op

        val coq_OpDateTimeEndOfYear : unary_op

        val coq_OpDateTimeFormatFromString : unary_op

        val coq_OpDateTimeFromString : unary_op

        val coq_OpDateTimeMax : unary_op

        val coq_OpDateTimeMin : unary_op

        val coq_OpDateTimeDurationFromString : unary_op

        val coq_OpDateTimeDurationFromSeconds : unary_op

        val coq_OpDateTimeDurationFromMinutes : unary_op

        val coq_OpDateTimeDurationFromHours : unary_op

        val coq_OpDateTimeDurationFromDays : unary_op

        val coq_OpDateTimeDurationFromWeeks : unary_op

        val coq_OpDateTimePeriodFromString : unary_op

        val coq_OpDateTimePeriodFromDays : unary_op

        val coq_OpDateTimePeriodFromWeeks : unary_op

        val coq_OpDateTimePeriodFromMonths : unary_op

        val coq_OpDateTimePeriodFromQuarters : unary_op

        val coq_OpDateTimePeriodFromYears : unary_op
       end

      module Binary :
       sig
        val date_time_format : binary_op

        val date_time_add : binary_op

        val date_time_subtract : binary_op

        val date_time_add_period : binary_op

        val date_time_subtract_period : binary_op

        val date_time_is_same : binary_op

        val date_time_is_before : binary_op

        val date_time_is_after : binary_op

        val date_time_diff : binary_op

        val coq_OpDateTimeFormat : binary_op

        val coq_OpDateTimeAdd : binary_op

        val coq_OpDateTimeSubtract : binary_op

        val coq_OpDateTimeIsBefore : binary_op

        val coq_OpDateTimeIsAfter : binary_op

        val coq_OpDateTimeDiff : binary_op
       end
     end
   end
 end

module QcertData :
 sig
  type json = JSON.json

  type data = Data.data

  type t = data

  val jnull : json

  val jnumber : float -> json

  val jbool : bool -> json

  val jstring : char list -> json

  val jarray : JSON.json list -> json

  val jobject : (char list * JSON.json) list -> json

  val dunit : data

  val dnat : int -> data

  val dfloat : float -> data

  val dbool : bool -> data

  val dstring : char list -> data

  val dcoll : Data.data list -> data

  val drec : (char list * Data.data) list -> data

  val dleft : data -> data

  val dright : data -> data

  val dbrand : brands -> data -> data

  val dsome : data -> data

  val dnone : data

  val dsuccess : data -> data

  val derror : data -> data
 end

module QcertOps :
 sig
  module ErgoData :
   sig
    type json = JSON.json

    type data = Data.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : JSON.json list -> json

    val jobject : (char list * JSON.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Data.data list -> data

    val drec : (char list * Data.data) list -> data

    val dleft : data -> data

    val dright : data -> data

    val dbrand : brands -> data -> data

    val dsome : data -> data

    val dnone : data

    val dsuccess : data -> data

    val derror : data -> data
   end

  module Unary :
   sig
    type op = unary_op

    type t = op

    module Double :
     sig
      val opuminus : op

      val opabs : op

      val oplog2 : op

      val opsqrt : op

      val opsum : op

      val opnummin : op

      val opnummax : op

      val opnummean : op
     end

    val opidentity : op

    val opneg : op

    val oprec : char list -> op

    val opdot : char list -> op

    val oprecremove : char list -> op

    val oprecproject : char list list -> op

    val opbag : op

    val opsingleton : op

    val opflatten : op

    val opdistinct : op

    val opcount : op

    val optostring : op

    val opsubstring : int -> int option -> op

    val oplike : char list -> op

    val opleft : op

    val opright : op

    val opbrand : brands -> op

    val opunbrand : op

    val opcast : brands -> op

    val eval :
      brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option
   end

  module Binary :
   sig
    type op = binary_op

    type t = op

    module Double :
     sig
      val opplus : op

      val opminus : op

      val opmult : op

      val opmin : op

      val opmax : op

      val opdiv : op

      val oppow : op

      val oplt : op

      val ople : op

      val opgt : op

      val opge : op
     end

    module Integer :
     sig
      val opplusi : op

      val opminusi : op

      val opmulti : op

      val opdivi : op

      val oplti : op

      val oplei : op
     end

    module DateTime :
     sig
      val opdateadd : op

      val opdatesubtract : op

      val opdateisbefore : op

      val opdateisafter : op

      val opdatediff : op
     end

    val opequal : op

    val oprecconcat : op

    val oprecmerge : op

    val opand : op

    val opor : op

    val opbagunion : op

    val opbagdiff : op

    val opbagmin : op

    val opbagmax : op

    val opnth : op

    val opcontains : op

    val opstringconcat : op

    val opstringjoin : op

    val eval :
      brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
      ErgoData.data option
   end
 end

module QcertCodeGen :
 sig
  type nnrc_expr = NNRC.nnrc

  val nnrc_optim : nnrc_expr -> nnrc_expr

  val nnrc_expr_let : var -> nnrc -> nnrc -> nnrc

  val eindent : int -> nstring

  val equotel_double : nstring

  val eeol_newline : nstring

  val javascript_identifier_sanitizer : char list -> char list

  type imp_ejson_function =
    (QcertBackend.ergo_foreign_ejson,
    QcertBackend.ergo_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function

  type imp_ejson_lib =
    (QcertBackend.ergo_foreign_ejson,
    QcertBackend.ergo_foreign_ejson_runtime_op) imp_ejson

  val nnrc_expr_to_imp_ejson_function :
    brand_model -> char list list -> CompLang.nnrc -> (enhanced_ejson,
    enhanced_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function

  val imp_function_to_javascript_ast :
    brand_model -> char list -> imp_ejson_function -> CompLang.js_ast

  val imp_function_table_to_javascript_ast :
    brand_model -> char list -> imp_ejson_lib -> CompLang.js_ast

  type ejavascript = javascript

  val nnrc_expr_to_imp_ejson :
    brand_model -> char list list -> (char list * CompLang.nnrc) ->
    (enhanced_ejson, enhanced_foreign_ejson_runtime_op) CompLang.imp_ejson

  val nnrc_expr_to_javascript_function :
    brand_model -> char list list -> (char list * CompLang.nnrc) ->
    CompLang.js_ast

  val nnrc_expr_to_javascript_function_table :
    brand_model -> char list list -> char list -> (char list * nnrc_expr)
    list -> CompLang.js_ast

  val js_ast_to_javascript : CompLang.js_ast -> javascript

  val javascript_of_inheritance : (char list * char list) list -> topdecl

  type java = CompLang.java

  val java_identifier_sanitizer : char list -> char list

  val nnrc_expr_to_java :
    NNRC.nnrc -> int -> int -> nstring -> nstring -> (char list * nstring)
    list -> (nstring * java_json) * int

  val nnrc_expr_java_unshadow :
    NNRC.nnrc -> int -> int -> nstring -> nstring -> var list ->
    (char list * nstring) list -> (nstring * java_json) * int

  val nnrc_expr_to_java_method :
    char list -> nnrc_expr -> int -> nstring -> nstring ->
    (char list * nstring) list -> nstring -> nstring

  type java_data = java_json

  val mk_java_data : nstring -> java_json

  val from_java_data : java_data -> nstring
 end

module QcertType :
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

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option

type qcert_data = QcertData.data

type qcert_type = QcertType.qtype
