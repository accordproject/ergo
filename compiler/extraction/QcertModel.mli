open BinaryOperators
open Data
open DataSystem
open DateTimeComponent
open ForeignType
open ForeignTyping
open QcertData
open QcertType
open QcertTyping
open TBrandModel
open UnaryOperators

val enhanced_basic_model : brand_model -> basic_model

module CompEnhanced :
 sig
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
