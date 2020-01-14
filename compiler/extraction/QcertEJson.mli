open Apply
open BrandRelation
open CoqLibAdd
open Datatypes
open DateTimeComponent
open EJson
open EJsonRuntimeOperators
open EmitUtil
open Encode
open EquivDec
open ForeignData
open ForeignEJson
open ForeignEJsonRuntime
open List0
open LogComponent
open MathComponent
open MonetaryAmountComponent
open QcertData
open String0
open ToString
open UriComponent

type enhanced_ejson = enhanced_data

val enhanced_foreign_ejson_obligation_3 : enhanced_ejson -> enhanced_ejson

val enhanced_foreign_ejson_obligation_1 : enhanced_ejson coq_EqDec

val enhanced_foreign_ejson_obligation_6 : enhanced_ejson coq_ToString

val enhanced_foreign_ejson : enhanced_ejson foreign_ejson

type enhanced_foreign_ejson_runtime_op =
| Coq_enhanced_ejson_uri of ejson_uri_runtime_op
| Coq_enhanced_ejson_log
| Coq_enhanced_ejson_math of ejson_math_runtime_op
| Coq_enhanced_ejson_date_time of ejson_date_time_runtime_op
| Coq_enhanced_ejson_monetary_amount of ejson_monetary_amount_runtime_op

val enhanced_foreign_ejson_runtime_op_tostring :
  enhanced_foreign_ejson_runtime_op -> char list

val enhanced_foreign_ejson_runtime_op_fromstring :
  char list -> enhanced_foreign_ejson_runtime_op option

val enhanced_ejson_uri_runtime_op_interp :
  ejson_uri_runtime_op -> enhanced_ejson ejson list -> enhanced_ejson ejson
  option

val onjstringunit :
  (char list -> unit) -> enhanced_ejson ejson -> enhanced_ejson ejson option

val enhanced_ejson_log_runtime_op_interp :
  enhanced_ejson ejson list -> enhanced_ejson ejson option

val enhanced_ejson_math_runtime_op_interp :
  ejson_math_runtime_op -> enhanced_ejson ejson list -> enhanced_ejson ejson
  option

val ejson_dates : enhanced_data ejson list -> coq_DATE_TIME list option

val enhanced_ejson_date_time_runtime_op_interp :
  ejson_date_time_runtime_op -> enhanced_data ejson list -> enhanced_data
  ejson option

val enhanced_ejson_monetary_amount_runtime_op_interp :
  ejson_monetary_amount_runtime_op -> enhanced_ejson ejson list ->
  enhanced_ejson ejson option

val enhanced_foreign_ejson_runtime_op_interp :
  enhanced_foreign_ejson_runtime_op -> enhanced_ejson ejson list ->
  enhanced_ejson ejson option

val ejsonEnumToString : brands -> enhanced_ejson ejson -> char list

val ejsonLeftToString : char list -> char list

val ejsonRightToString : char list -> char list

val ejsonArrayToString : char list list -> char list

val ejsonObjectToString : (char list * char list) list -> char list

val ejsonToString : enhanced_ejson ejson -> char list

val ejsonToText : enhanced_ejson ejson -> char list

val enhanced_foreign_ejson_runtime_obligation_1 :
  enhanced_foreign_ejson_runtime_op coq_EqDec

val enhanced_foreign_ejson_runtime_obligation_2 :
  enhanced_foreign_ejson_runtime_op coq_ToString

val enhanced_foreign_ejson_runtime_obligation_3 :
  enhanced_foreign_ejson_runtime_op -> enhanced_ejson ejson list ->
  enhanced_ejson ejson option

val enhanced_foreign_ejson_runtime_obligation_4 :
  enhanced_ejson ejson -> char list

val enhanced_foreign_ejson_runtime_obligation_5 :
  char list -> enhanced_foreign_ejson_runtime_op option

val enhanced_foreign_ejson_runtime_obligation_6 :
  enhanced_ejson ejson -> char list

val enhanced_foreign_ejson_runtime :
  (enhanced_foreign_ejson_runtime_op, enhanced_ejson) foreign_ejson_runtime
