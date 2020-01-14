open DateTimeComponent
open ForeignData
open ForeignDataToEJson
open ForeignOperators
open ForeignToEJsonRuntime
open MathComponent
open MonetaryAmountComponent
open QcertData
open QcertEJson
open UriComponent

(** val enhanced_foreign_to_ejson_obligation_1 :
    enhanced_ejson -> foreign_data_model **)

let enhanced_foreign_to_ejson_obligation_1 j =
  Obj.magic j

(** val enhanced_foreign_to_ejson_obligation_2 :
    foreign_data_model -> enhanced_ejson **)

let enhanced_foreign_to_ejson_obligation_2 fd =
  Obj.magic fd

(** val enhanced_foreign_to_ejson :
    (enhanced_ejson, enhanced_foreign_ejson_runtime_op) foreign_to_ejson **)

let enhanced_foreign_to_ejson =
  { foreign_to_ejson_runtime = enhanced_foreign_ejson_runtime;
    foreign_to_ejson_to_data = enhanced_foreign_to_ejson_obligation_1;
    foreign_to_ejson_from_data = enhanced_foreign_to_ejson_obligation_2 }

(** val unary_op_to_ejson :
    enhanced_unary_op -> enhanced_foreign_ejson_runtime_op **)

let unary_op_to_ejson = function
| Coq_enhanced_unary_uri_op uop ->
  (match uop with
   | Coq_uop_uri_encode -> Coq_enhanced_ejson_uri EJsonRuntimeUriEncode
   | Coq_uop_uri_decode -> Coq_enhanced_ejson_uri EJsonRuntimeUriDecode)
| Coq_enhanced_unary_log_op -> Coq_enhanced_ejson_log
| Coq_enhanced_unary_math_op mop ->
  (match mop with
   | Coq_uop_math_float_of_string ->
     Coq_enhanced_ejson_math EJsonRuntimeFloatOfString
   | Coq_uop_math_acos -> Coq_enhanced_ejson_math EJsonRuntimeAcos
   | Coq_uop_math_asin -> Coq_enhanced_ejson_math EJsonRuntimeAsin
   | Coq_uop_math_atan -> Coq_enhanced_ejson_math EJsonRuntimeAtan
   | Coq_uop_math_cos -> Coq_enhanced_ejson_math EJsonRuntimeCos
   | Coq_uop_math_cosh -> Coq_enhanced_ejson_math EJsonRuntimeCosh
   | Coq_uop_math_sin -> Coq_enhanced_ejson_math EJsonRuntimeSin
   | Coq_uop_math_sinh -> Coq_enhanced_ejson_math EJsonRuntimeSinh
   | Coq_uop_math_tan -> Coq_enhanced_ejson_math EJsonRuntimeTan
   | Coq_uop_math_tanh -> Coq_enhanced_ejson_math EJsonRuntimeTanh)
| Coq_enhanced_unary_date_time_op dop ->
  (match dop with
   | Coq_uop_date_time_get_seconds ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetSeconds
   | Coq_uop_date_time_get_minutes ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetMinutes
   | Coq_uop_date_time_get_hours ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetHours
   | Coq_uop_date_time_get_days ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetDays
   | Coq_uop_date_time_get_weeks ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetWeeks
   | Coq_uop_date_time_get_months ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetMonths
   | Coq_uop_date_time_get_quarters ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetQuarters
   | Coq_uop_date_time_get_years ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeGetYears
   | Coq_uop_date_time_start_of_day ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfDay
   | Coq_uop_date_time_start_of_week ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfWeek
   | Coq_uop_date_time_start_of_month ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfMonth
   | Coq_uop_date_time_start_of_quarter ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfQuarter
   | Coq_uop_date_time_start_of_year ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfYear
   | Coq_uop_date_time_end_of_day ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfDay
   | Coq_uop_date_time_end_of_week ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfWeek
   | Coq_uop_date_time_end_of_month ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfMonth
   | Coq_uop_date_time_end_of_quarter ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfQuarter
   | Coq_uop_date_time_end_of_year ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfYear
   | Coq_uop_date_time_format_from_string ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeFormatFromString
   | Coq_uop_date_time_from_string ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeFromString
   | Coq_uop_date_time_max ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeMax
   | Coq_uop_date_time_min ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeMin
   | Coq_uop_date_time_duration_amount ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationAmount
   | Coq_uop_date_time_duration_from_string ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromString
   | Coq_uop_date_time_duration_from_seconds ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromSeconds
   | Coq_uop_date_time_duration_from_minutes ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromMinutes
   | Coq_uop_date_time_duration_from_hours ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromHours
   | Coq_uop_date_time_duration_from_days ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromDays
   | Coq_uop_date_time_duration_from_weeks ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromWeeks
   | Coq_uop_date_time_period_from_string ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromString
   | Coq_uop_date_time_period_from_days ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromDays
   | Coq_uop_date_time_period_from_weeks ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromWeeks
   | Coq_uop_date_time_period_from_months ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromMonths
   | Coq_uop_date_time_period_from_quarters ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromQuarters
   | Coq_uop_date_time_period_from_years ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromYears)

(** val binary_op_to_ejson :
    enhanced_binary_op -> enhanced_foreign_ejson_runtime_op **)

let binary_op_to_ejson = function
| Coq_enhanced_binary_math_op -> Coq_enhanced_ejson_math EJsonRuntimeAtan2
| Coq_enhanced_binary_date_time_op dop ->
  (match dop with
   | Coq_bop_date_time_format ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeFormat
   | Coq_bop_date_time_add ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeAdd
   | Coq_bop_date_time_subtract ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeSubtract
   | Coq_bop_date_time_add_period ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeAddPeriod
   | Coq_bop_date_time_subtract_period ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeSubtractPeriod
   | Coq_bop_date_time_is_same ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeIsSame
   | Coq_bop_date_time_is_before ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeIsBefore
   | Coq_bop_date_time_is_after ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeIsAfter
   | Coq_bop_date_time_diff ->
     Coq_enhanced_ejson_date_time EJsonRuntimeDateTimeDiff)
| Coq_enhanced_binary_monetary_amount_op mop ->
  (match mop with
   | Coq_bop_monetary_amount_format ->
     Coq_enhanced_ejson_monetary_amount EJsonRuntimeMonetaryAmountFormat
   | Coq_bop_monetary_code_format ->
     Coq_enhanced_ejson_monetary_amount EJsonRuntimeMonetaryCodeFormat)

(** val enhanced_foreign_to_ejson_runtime_obligation_1 :
    foreign_operators_unary -> enhanced_foreign_ejson_runtime_op **)

let enhanced_foreign_to_ejson_runtime_obligation_1 uop =
  unary_op_to_ejson (Obj.magic uop)

(** val enhanced_foreign_to_ejson_runtime_obligation_3 :
    foreign_operators_binary -> enhanced_foreign_ejson_runtime_op **)

let enhanced_foreign_to_ejson_runtime_obligation_3 bop =
  binary_op_to_ejson (Obj.magic bop)

(** val enhanced_foreign_to_ejson_runtime :
    (enhanced_ejson, enhanced_foreign_ejson_runtime_op)
    foreign_to_ejson_runtime **)

let enhanced_foreign_to_ejson_runtime =
  { foreign_to_ejson_runtime_of_unary_op =
    enhanced_foreign_to_ejson_runtime_obligation_1;
    foreign_to_ejson_runtime_of_binary_op =
    enhanced_foreign_to_ejson_runtime_obligation_3 }
