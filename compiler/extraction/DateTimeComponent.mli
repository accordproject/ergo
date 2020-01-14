open CoqLibAdd
open EquivDec
open ForeignData
open Java
open NativeString

type coq_DATE_TIME_FORMAT = Date_time_component.date_time_format

type coq_DATE_TIME_DURATION = Date_time_component.duration

type coq_DATE_TIME_PERIOD = Date_time_component.period

type coq_DATE_TIME = Date_time_component.dateTime

val date_time_format_foreign_data_obligation_3 :
  coq_DATE_TIME_FORMAT -> coq_DATE_TIME_FORMAT

val date_time_format_foreign_data_obligation_1 :
  coq_DATE_TIME_FORMAT coq_EqDec

val date_time_format_foreign_data_obligation_6 :
  coq_DATE_TIME_FORMAT coq_ToString

val date_time_format_foreign_data : foreign_data

val date_time_duration_foreign_data_obligation_3 :
  coq_DATE_TIME_DURATION -> coq_DATE_TIME_DURATION

val date_time_duration_foreign_data_obligation_1 :
  coq_DATE_TIME_DURATION coq_EqDec

val date_time_duration_foreign_data_obligation_6 :
  coq_DATE_TIME_DURATION coq_ToString

val date_time_duration_foreign_data : foreign_data

val date_time_period_foreign_data_obligation_3 :
  coq_DATE_TIME_PERIOD -> coq_DATE_TIME_PERIOD

val date_time_period_foreign_data_obligation_1 :
  coq_DATE_TIME_PERIOD coq_EqDec

val date_time_period_foreign_data_obligation_6 :
  coq_DATE_TIME_PERIOD coq_ToString

val date_time_period_foreign_data : foreign_data

val date_time_foreign_data_obligation_3 : coq_DATE_TIME -> coq_DATE_TIME

val date_time_foreign_data_obligation_1 : coq_DATE_TIME coq_EqDec

val date_time_foreign_data_obligation_6 : coq_DATE_TIME coq_ToString

val date_time_foreign_data : foreign_data

type date_time_unary_op =
| Coq_uop_date_time_get_seconds
| Coq_uop_date_time_get_minutes
| Coq_uop_date_time_get_hours
| Coq_uop_date_time_get_days
| Coq_uop_date_time_get_weeks
| Coq_uop_date_time_get_months
| Coq_uop_date_time_get_quarters
| Coq_uop_date_time_get_years
| Coq_uop_date_time_start_of_day
| Coq_uop_date_time_start_of_week
| Coq_uop_date_time_start_of_month
| Coq_uop_date_time_start_of_quarter
| Coq_uop_date_time_start_of_year
| Coq_uop_date_time_end_of_day
| Coq_uop_date_time_end_of_week
| Coq_uop_date_time_end_of_month
| Coq_uop_date_time_end_of_quarter
| Coq_uop_date_time_end_of_year
| Coq_uop_date_time_format_from_string
| Coq_uop_date_time_from_string
| Coq_uop_date_time_max
| Coq_uop_date_time_min
| Coq_uop_date_time_duration_amount
| Coq_uop_date_time_duration_from_string
| Coq_uop_date_time_duration_from_seconds
| Coq_uop_date_time_duration_from_minutes
| Coq_uop_date_time_duration_from_hours
| Coq_uop_date_time_duration_from_days
| Coq_uop_date_time_duration_from_weeks
| Coq_uop_date_time_period_from_string
| Coq_uop_date_time_period_from_days
| Coq_uop_date_time_period_from_weeks
| Coq_uop_date_time_period_from_months
| Coq_uop_date_time_period_from_quarters
| Coq_uop_date_time_period_from_years

type date_time_binary_op =
| Coq_bop_date_time_format
| Coq_bop_date_time_add
| Coq_bop_date_time_subtract
| Coq_bop_date_time_add_period
| Coq_bop_date_time_subtract_period
| Coq_bop_date_time_is_same
| Coq_bop_date_time_is_before
| Coq_bop_date_time_is_after
| Coq_bop_date_time_diff

val date_time_unary_op_tostring : date_time_unary_op -> char list

val date_time_binary_op_tostring : date_time_binary_op -> char list

val cname : nstring

val date_time_to_java_unary_op :
  int -> nstring -> nstring -> date_time_unary_op -> java_json -> java_json

val date_time_to_java_binary_op :
  int -> nstring -> nstring -> date_time_binary_op -> java_json -> java_json
  -> java_json

type ejson_date_time_runtime_op =
| EJsonRuntimeDateTimeGetSeconds
| EJsonRuntimeDateTimeGetMinutes
| EJsonRuntimeDateTimeGetHours
| EJsonRuntimeDateTimeGetDays
| EJsonRuntimeDateTimeGetWeeks
| EJsonRuntimeDateTimeGetMonths
| EJsonRuntimeDateTimeGetQuarters
| EJsonRuntimeDateTimeGetYears
| EJsonRuntimeDateTimeStartOfDay
| EJsonRuntimeDateTimeStartOfWeek
| EJsonRuntimeDateTimeStartOfMonth
| EJsonRuntimeDateTimeStartOfQuarter
| EJsonRuntimeDateTimeStartOfYear
| EJsonRuntimeDateTimeEndOfDay
| EJsonRuntimeDateTimeEndOfWeek
| EJsonRuntimeDateTimeEndOfMonth
| EJsonRuntimeDateTimeEndOfQuarter
| EJsonRuntimeDateTimeEndOfYear
| EJsonRuntimeDateTimeFormatFromString
| EJsonRuntimeDateTimeFromString
| EJsonRuntimeDateTimeMax
| EJsonRuntimeDateTimeMin
| EJsonRuntimeDateTimeDurationAmount
| EJsonRuntimeDateTimeDurationFromString
| EJsonRuntimeDateTimePeriodFromString
| EJsonRuntimeDateTimeDurationFromSeconds
| EJsonRuntimeDateTimeDurationFromMinutes
| EJsonRuntimeDateTimeDurationFromHours
| EJsonRuntimeDateTimeDurationFromDays
| EJsonRuntimeDateTimeDurationFromWeeks
| EJsonRuntimeDateTimePeriodFromDays
| EJsonRuntimeDateTimePeriodFromWeeks
| EJsonRuntimeDateTimePeriodFromMonths
| EJsonRuntimeDateTimePeriodFromQuarters
| EJsonRuntimeDateTimePeriodFromYears
| EJsonRuntimeDateTimeFormat
| EJsonRuntimeDateTimeAdd
| EJsonRuntimeDateTimeSubtract
| EJsonRuntimeDateTimeAddPeriod
| EJsonRuntimeDateTimeSubtractPeriod
| EJsonRuntimeDateTimeIsSame
| EJsonRuntimeDateTimeIsBefore
| EJsonRuntimeDateTimeIsAfter
| EJsonRuntimeDateTimeDiff

val ejson_date_time_runtime_op_tostring :
  ejson_date_time_runtime_op -> char list

val ejson_date_time_runtime_op_fromstring :
  char list -> ejson_date_time_runtime_op option
