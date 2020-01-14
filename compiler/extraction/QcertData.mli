open BrandRelation
open CoqLibAdd
open Data
open DateTimeComponent
open EmitUtil
open EquivDec
open ForeignData
open ForeignOperators
open ForeignRuntime
open Lift
open LiftIterators
open List0
open LogComponent
open MathComponent
open MonetaryAmountComponent
open String0
open ToString
open UriComponent

type enhanced_data =
| Coq_enhanceddateTimeformat of coq_DATE_TIME_FORMAT
| Coq_enhanceddateTime of coq_DATE_TIME
| Coq_enhanceddateTimeduration of coq_DATE_TIME_DURATION
| Coq_enhanceddateTimeperiod of coq_DATE_TIME_PERIOD

val enhanceddateTime_now : coq_DATE_TIME

val enhanced_foreign_data_obligation_3 : enhanced_data -> enhanced_data

val enhanced_foreign_data_obligation_1 : enhanced_data coq_EqDec

val enhanced_foreign_data_obligation_6 : enhanced_data coq_ToString

val enhanced_foreign_data : foreign_data

val denhanceddateTimeformat : coq_DATE_TIME_FORMAT -> data

val denhanceddateTime : coq_DATE_TIME -> data

val denhanceddateTimeduration : coq_DATE_TIME_DURATION -> data

val denhanceddateTimeperiod : coq_DATE_TIME_PERIOD -> data

type enhanced_unary_op =
| Coq_enhanced_unary_uri_op of uri_unary_op
| Coq_enhanced_unary_log_op
| Coq_enhanced_unary_math_op of math_unary_op
| Coq_enhanced_unary_date_time_op of date_time_unary_op

val onddateTime : (coq_DATE_TIME -> 'a1) -> data -> 'a1 option

val lift_dateTimeList : data list -> coq_DATE_TIME list option

val onddateTimeList :
  (coq_DATE_TIME list -> coq_DATE_TIME) -> data -> coq_DATE_TIME option

val onddateTimeduration :
  (coq_DATE_TIME_DURATION -> 'a1) -> data -> 'a1 option

val onddateTimeDurationNat : (int -> 'a1) -> data -> 'a1 option

val onddateTimePeriodNat : (int -> 'a1) -> data -> 'a1 option

val ondstring : (char list -> 'a1) -> data -> 'a1 option

val ondstringfloatopt : (char list -> float option) -> data -> data option

val ondstringunit : (char list -> unit) -> data -> data option

val ondstringstring : (char list -> char list) -> data -> data option

val ondfloat : (float -> 'a1) -> data -> 'a1 option

val uri_unary_op_interp : uri_unary_op -> data -> data option

val log_unary_op_interp : data -> data option

val math_unary_op_interp : math_unary_op -> data -> data option

val date_time_unary_op_interp : date_time_unary_op -> data -> data option

val enhanced_unary_op_interp :
  brand_relation_t -> enhanced_unary_op -> data -> data option

val enumToString : brands -> data -> char list

val dataToString : data -> char list

val dataToText : data -> char list

type enhanced_binary_op =
| Coq_enhanced_binary_math_op
| Coq_enhanced_binary_date_time_op of date_time_binary_op
| Coq_enhanced_binary_monetary_amount_op of monetary_amount_binary_op

val ondfloat2 : (float -> float -> 'a1) -> data -> data -> 'a1 option

val onddateTime2 :
  (coq_DATE_TIME -> coq_DATE_TIME -> 'a1) -> data -> data -> 'a1 option

val rondbooldateTime2 :
  (coq_DATE_TIME -> coq_DATE_TIME -> bool) -> data -> data -> data option

val math_binary_op_interp : data -> data -> data option

val date_time_binary_op_interp :
  date_time_binary_op -> data -> data -> data option

val monetary_amount_binary_op_interp :
  monetary_amount_binary_op -> data -> data -> data option

val enhanced_binary_op_interp :
  brand_relation_t -> enhanced_binary_op -> data -> data -> data option

val enhanced_foreign_operators_obligation_1 : enhanced_unary_op coq_EqDec

val enhanced_foreign_operators_obligation_2 : enhanced_unary_op coq_ToString

val enhanced_foreign_operators_obligation_4 : enhanced_binary_op coq_EqDec

val enhanced_foreign_operators_obligation_5 : enhanced_binary_op coq_ToString

val enhanced_foreign_operators : foreign_operators

val enhanced_foreign_runtime : foreign_runtime
