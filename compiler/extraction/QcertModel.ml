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

(** val enhanced_basic_model : brand_model -> basic_model **)

let enhanced_basic_model model =
  { basic_model_runtime = enhanced_foreign_runtime;
    basic_model_foreign_type = enhanced_foreign_type;
    basic_model_brand_model = model; basic_model_foreign_typing =
    (enhanced_foreign_typing model) }

module CompEnhanced =
 struct
  module Enhanced =
   struct
    module Model =
     struct
      (** val basic_model : brand_model -> basic_model **)

      let basic_model =
        enhanced_basic_model

      (** val foreign_type : foreign_type **)

      let foreign_type =
        enhanced_foreign_type

      (** val foreign_typing : brand_model -> foreign_typing **)

      let foreign_typing =
        enhanced_foreign_typing
     end

    module Data =
     struct
      (** val ddate_time : coq_DATE_TIME -> data **)

      let ddate_time d =
        Coq_dforeign (Obj.magic (Coq_enhanceddateTime d))

      (** val ddate_time_duration : coq_DATE_TIME_DURATION -> data **)

      let ddate_time_duration d =
        Coq_dforeign (Obj.magic (Coq_enhanceddateTimeduration d))

      (** val ddate_time_period : coq_DATE_TIME_PERIOD -> data **)

      let ddate_time_period d =
        Coq_dforeign (Obj.magic (Coq_enhanceddateTimeperiod d))
     end

    module Ops =
     struct
      module Unary =
       struct
        (** val date_time_get_seconds : unary_op **)

        let date_time_get_seconds =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_seconds))

        (** val date_time_get_minutes : unary_op **)

        let date_time_get_minutes =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_minutes))

        (** val date_time_get_hours : unary_op **)

        let date_time_get_hours =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_hours))

        (** val date_time_get_days : unary_op **)

        let date_time_get_days =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_days))

        (** val date_time_get_weeks : unary_op **)

        let date_time_get_weeks =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_weeks))

        (** val date_time_get_months : unary_op **)

        let date_time_get_months =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_months))

        (** val date_time_get_quarters : unary_op **)

        let date_time_get_quarters =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_quarters))

        (** val date_time_get_years : unary_op **)

        let date_time_get_years =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_get_years))

        (** val date_time_start_of_day : unary_op **)

        let date_time_start_of_day =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_start_of_day))

        (** val date_time_start_of_week : unary_op **)

        let date_time_start_of_week =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_start_of_week))

        (** val date_time_start_of_month : unary_op **)

        let date_time_start_of_month =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_start_of_month))

        (** val date_time_start_of_quarter : unary_op **)

        let date_time_start_of_quarter =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_start_of_quarter))

        (** val date_time_start_of_year : unary_op **)

        let date_time_start_of_year =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_start_of_year))

        (** val date_time_end_of_day : unary_op **)

        let date_time_end_of_day =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_end_of_day))

        (** val date_time_end_of_week : unary_op **)

        let date_time_end_of_week =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_end_of_week))

        (** val date_time_end_of_month : unary_op **)

        let date_time_end_of_month =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_end_of_month))

        (** val date_time_end_of_quarter : unary_op **)

        let date_time_end_of_quarter =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_end_of_quarter))

        (** val date_time_end_of_year : unary_op **)

        let date_time_end_of_year =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_end_of_year))

        (** val date_time_format_from_string : unary_op **)

        let date_time_format_from_string =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_format_from_string))

        (** val date_time_from_string : unary_op **)

        let date_time_from_string =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_from_string))

        (** val date_time_min : unary_op **)

        let date_time_min =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_min))

        (** val date_time_max : unary_op **)

        let date_time_max =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_max))

        (** val date_time_duration_amount : unary_op **)

        let date_time_duration_amount =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_amount))

        (** val date_time_duration_from_string : unary_op **)

        let date_time_duration_from_string =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_string))

        (** val date_time_duration_from_seconds : unary_op **)

        let date_time_duration_from_seconds =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_seconds))

        (** val date_time_duration_from_minutes : unary_op **)

        let date_time_duration_from_minutes =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_minutes))

        (** val date_time_duration_from_hours : unary_op **)

        let date_time_duration_from_hours =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_hours))

        (** val date_time_duration_from_days : unary_op **)

        let date_time_duration_from_days =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_days))

        (** val date_time_duration_from_weeks : unary_op **)

        let date_time_duration_from_weeks =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_duration_from_weeks))

        (** val date_time_period_from_string : unary_op **)

        let date_time_period_from_string =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_string))

        (** val date_time_period_from_days : unary_op **)

        let date_time_period_from_days =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_days))

        (** val date_time_period_from_weeks : unary_op **)

        let date_time_period_from_weeks =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_weeks))

        (** val date_time_period_from_months : unary_op **)

        let date_time_period_from_months =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_months))

        (** val date_time_period_from_quarters : unary_op **)

        let date_time_period_from_quarters =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_quarters))

        (** val date_time_period_from_years : unary_op **)

        let date_time_period_from_years =
          OpForeignUnary
            (Obj.magic (Coq_enhanced_unary_date_time_op
              Coq_uop_date_time_period_from_years))

        (** val coq_OpDateTimeGetSeconds : unary_op **)

        let coq_OpDateTimeGetSeconds =
          date_time_get_seconds

        (** val coq_OpDateTimeGetMinutes : unary_op **)

        let coq_OpDateTimeGetMinutes =
          date_time_get_minutes

        (** val coq_OpDateTimeGetHours : unary_op **)

        let coq_OpDateTimeGetHours =
          date_time_get_hours

        (** val coq_OpDateTimeGetDays : unary_op **)

        let coq_OpDateTimeGetDays =
          date_time_get_days

        (** val coq_OpDateTimeGetWeeks : unary_op **)

        let coq_OpDateTimeGetWeeks =
          date_time_get_weeks

        (** val coq_OpDateTimeGetMonths : unary_op **)

        let coq_OpDateTimeGetMonths =
          date_time_get_months

        (** val coq_OpDateTimeGetQuarters : unary_op **)

        let coq_OpDateTimeGetQuarters =
          date_time_get_quarters

        (** val coq_OpDateTimeGetYears : unary_op **)

        let coq_OpDateTimeGetYears =
          date_time_get_years

        (** val coq_OpDateTimeStartOfDay : unary_op **)

        let coq_OpDateTimeStartOfDay =
          date_time_start_of_day

        (** val coq_OpDateTimeStartOfWeek : unary_op **)

        let coq_OpDateTimeStartOfWeek =
          date_time_start_of_week

        (** val coq_OpDateTimeStartOfMonth : unary_op **)

        let coq_OpDateTimeStartOfMonth =
          date_time_start_of_month

        (** val coq_OpDateTimeStartOfQuarter : unary_op **)

        let coq_OpDateTimeStartOfQuarter =
          date_time_start_of_quarter

        (** val coq_OpDateTimeStartOfYear : unary_op **)

        let coq_OpDateTimeStartOfYear =
          date_time_start_of_year

        (** val coq_OpDateTimeEndOfDay : unary_op **)

        let coq_OpDateTimeEndOfDay =
          date_time_end_of_day

        (** val coq_OpDateTimeEndOfWeek : unary_op **)

        let coq_OpDateTimeEndOfWeek =
          date_time_end_of_week

        (** val coq_OpDateTimeEndOfMonth : unary_op **)

        let coq_OpDateTimeEndOfMonth =
          date_time_end_of_month

        (** val coq_OpDateTimeEndOfQuarter : unary_op **)

        let coq_OpDateTimeEndOfQuarter =
          date_time_end_of_quarter

        (** val coq_OpDateTimeEndOfYear : unary_op **)

        let coq_OpDateTimeEndOfYear =
          date_time_end_of_year

        (** val coq_OpDateTimeFormatFromString : unary_op **)

        let coq_OpDateTimeFormatFromString =
          date_time_format_from_string

        (** val coq_OpDateTimeFromString : unary_op **)

        let coq_OpDateTimeFromString =
          date_time_from_string

        (** val coq_OpDateTimeMax : unary_op **)

        let coq_OpDateTimeMax =
          date_time_max

        (** val coq_OpDateTimeMin : unary_op **)

        let coq_OpDateTimeMin =
          date_time_min

        (** val coq_OpDateTimeDurationFromString : unary_op **)

        let coq_OpDateTimeDurationFromString =
          date_time_duration_from_string

        (** val coq_OpDateTimeDurationFromSeconds : unary_op **)

        let coq_OpDateTimeDurationFromSeconds =
          date_time_duration_from_seconds

        (** val coq_OpDateTimeDurationFromMinutes : unary_op **)

        let coq_OpDateTimeDurationFromMinutes =
          date_time_duration_from_minutes

        (** val coq_OpDateTimeDurationFromHours : unary_op **)

        let coq_OpDateTimeDurationFromHours =
          date_time_duration_from_hours

        (** val coq_OpDateTimeDurationFromDays : unary_op **)

        let coq_OpDateTimeDurationFromDays =
          date_time_duration_from_days

        (** val coq_OpDateTimeDurationFromWeeks : unary_op **)

        let coq_OpDateTimeDurationFromWeeks =
          date_time_duration_from_weeks

        (** val coq_OpDateTimePeriodFromString : unary_op **)

        let coq_OpDateTimePeriodFromString =
          date_time_period_from_string

        (** val coq_OpDateTimePeriodFromDays : unary_op **)

        let coq_OpDateTimePeriodFromDays =
          date_time_period_from_days

        (** val coq_OpDateTimePeriodFromWeeks : unary_op **)

        let coq_OpDateTimePeriodFromWeeks =
          date_time_period_from_weeks

        (** val coq_OpDateTimePeriodFromMonths : unary_op **)

        let coq_OpDateTimePeriodFromMonths =
          date_time_period_from_months

        (** val coq_OpDateTimePeriodFromQuarters : unary_op **)

        let coq_OpDateTimePeriodFromQuarters =
          date_time_period_from_quarters

        (** val coq_OpDateTimePeriodFromYears : unary_op **)

        let coq_OpDateTimePeriodFromYears =
          date_time_period_from_years
       end

      module Binary =
       struct
        (** val date_time_format : binary_op **)

        let date_time_format =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_format))

        (** val date_time_add : binary_op **)

        let date_time_add =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_add))

        (** val date_time_subtract : binary_op **)

        let date_time_subtract =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_subtract))

        (** val date_time_add_period : binary_op **)

        let date_time_add_period =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_add_period))

        (** val date_time_subtract_period : binary_op **)

        let date_time_subtract_period =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_subtract_period))

        (** val date_time_is_same : binary_op **)

        let date_time_is_same =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_is_same))

        (** val date_time_is_before : binary_op **)

        let date_time_is_before =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_is_before))

        (** val date_time_is_after : binary_op **)

        let date_time_is_after =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_is_after))

        (** val date_time_diff : binary_op **)

        let date_time_diff =
          OpForeignBinary
            (Obj.magic (Coq_enhanced_binary_date_time_op
              Coq_bop_date_time_diff))

        (** val coq_OpDateTimeFormat : binary_op **)

        let coq_OpDateTimeFormat =
          date_time_format

        (** val coq_OpDateTimeAdd : binary_op **)

        let coq_OpDateTimeAdd =
          date_time_add

        (** val coq_OpDateTimeSubtract : binary_op **)

        let coq_OpDateTimeSubtract =
          date_time_subtract

        (** val coq_OpDateTimeIsBefore : binary_op **)

        let coq_OpDateTimeIsBefore =
          date_time_is_before

        (** val coq_OpDateTimeIsAfter : binary_op **)

        let coq_OpDateTimeIsAfter =
          date_time_is_after

        (** val coq_OpDateTimeDiff : binary_op **)

        let coq_OpDateTimeDiff =
          date_time_diff
       end
     end
   end
 end
