(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import String.

Require Import Qcert.Utils.Utils.
Require Import Qcert.EJson.EJsonSystem.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.Translation.Model.ForeignDataToEJson.
Require Import Qcert.Translation.Model.DataToEJson.
Require Import Qcert.Translation.Operators.ForeignToEJsonRuntime.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Require Import QcertData.
Require Import QcertEJson.

Import ListNotations.
Local Open Scope list_scope.

Program Instance enhanced_foreign_to_ejson : foreign_to_ejson
  := mk_foreign_to_ejson enhanced_foreign_runtime enhanced_foreign_ejson _ _ _ _.
Next Obligation.
  exact j. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.
Next Obligation.
  exact fd. (* XXX enhanced_ejson is the same as enhanced_data *)
Defined.

Definition unary_op_to_ejson (op:enhanced_unary_op) : enhanced_foreign_ejson_runtime_op :=
  match op with
  | enhanced_unary_uri_op uop =>
    match uop with
    | uop_uri_encode => enhanced_ejson_uri EJsonRuntimeUriEncode
    | uop_uri_decode => enhanced_ejson_uri EJsonRuntimeUriDecode
    end
  | enhanced_unary_log_op lop =>
    match lop with
    | uop_log_string => enhanced_ejson_log EJsonRuntimeLogString
    end
  | enhanced_unary_math_op mop =>
    match mop with
    | uop_math_float_of_string => enhanced_ejson_math EJsonRuntimeFloatOfString
    | uop_math_acos => enhanced_ejson_math EJsonRuntimeAcos
    | uop_math_asin => enhanced_ejson_math EJsonRuntimeAsin
    | uop_math_atan => enhanced_ejson_math EJsonRuntimeAtan
    | uop_math_cos => enhanced_ejson_math EJsonRuntimeCos
    | uop_math_cosh => enhanced_ejson_math EJsonRuntimeCosh
    | uop_math_sin => enhanced_ejson_math EJsonRuntimeSin
    | uop_math_sinh => enhanced_ejson_math EJsonRuntimeSinh
    | uop_math_tan => enhanced_ejson_math EJsonRuntimeTan
    | uop_math_tanh => enhanced_ejson_math EJsonRuntimeTanh
    end
  | enhanced_unary_date_time_op dop =>
    match dop with
    | uop_date_time_get_seconds => enhanced_ejson_date_time EJsonRuntimeDateTimeGetSeconds
    | uop_date_time_get_minutes => enhanced_ejson_date_time EJsonRuntimeDateTimeGetMinutes
    | uop_date_time_get_hours => enhanced_ejson_date_time EJsonRuntimeDateTimeGetHours
    | uop_date_time_get_days => enhanced_ejson_date_time EJsonRuntimeDateTimeGetDays
    | uop_date_time_get_weeks => enhanced_ejson_date_time EJsonRuntimeDateTimeGetWeeks
    | uop_date_time_get_months => enhanced_ejson_date_time EJsonRuntimeDateTimeGetMonths
    | uop_date_time_get_quarters => enhanced_ejson_date_time EJsonRuntimeDateTimeGetQuarters
    | uop_date_time_get_years => enhanced_ejson_date_time EJsonRuntimeDateTimeGetYears
    | uop_date_time_start_of_day => enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfDay
    | uop_date_time_start_of_week => enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfWeek
    | uop_date_time_start_of_month => enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfMonth
    | uop_date_time_start_of_quarter => enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfQuarter
    | uop_date_time_start_of_year => enhanced_ejson_date_time EJsonRuntimeDateTimeStartOfYear
    | uop_date_time_end_of_day => enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfDay
    | uop_date_time_end_of_week => enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfWeek
    | uop_date_time_end_of_month => enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfMonth
    | uop_date_time_end_of_quarter => enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfQuarter
    | uop_date_time_end_of_year => enhanced_ejson_date_time EJsonRuntimeDateTimeEndOfYear
    | uop_date_time_format_from_string => enhanced_ejson_date_time EJsonRuntimeDateTimeFormatFromString
    | uop_date_time_from_string => enhanced_ejson_date_time EJsonRuntimeDateTimeFromString
    | uop_date_time_max => enhanced_ejson_date_time EJsonRuntimeDateTimeMax
    | uop_date_time_min => enhanced_ejson_date_time EJsonRuntimeDateTimeMin
    | uop_date_time_duration_amount => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationAmount
    | uop_date_time_duration_from_string => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromString
    | uop_date_time_duration_from_seconds => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromSeconds
    | uop_date_time_duration_from_minutes => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromMinutes
    | uop_date_time_duration_from_hours => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromHours
    | uop_date_time_duration_from_days => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromDays
    | uop_date_time_duration_from_weeks => enhanced_ejson_date_time EJsonRuntimeDateTimeDurationFromWeeks
    | uop_date_time_period_from_string => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromString
    | uop_date_time_period_from_days => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromDays
    | uop_date_time_period_from_weeks => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromWeeks
    | uop_date_time_period_from_months => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromMonths
    | uop_date_time_period_from_quarters => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromQuarters
    | uop_date_time_period_from_years => enhanced_ejson_date_time EJsonRuntimeDateTimePeriodFromYears
    end
  end.

Lemma ejson_lifted_dbag_comm l:
  lift_map (onddateTime (fun x => x)) l =
  ejson_dates (map data_to_ejson l).
Proof.
  induction l; simpl; try reflexivity.
  unfold onddateTime in *; simpl.
  destruct a; try reflexivity.
  destruct f; try reflexivity.
  unfold lift; simpl.
  assert ((@lift_map (@data enhanced_foreign_data) DATE_TIME
             (fun d : @data enhanced_foreign_data =>
              match d return (option DATE_TIME) with
              | dunit => @None DATE_TIME
              | dnat _ => @None DATE_TIME
              | dfloat _ => @None DATE_TIME
              | dbool _ => @None DATE_TIME
              | dstring _ => @None DATE_TIME
              | dcoll _ => @None DATE_TIME
              | drec _ => @None DATE_TIME
              | dleft _ => @None DATE_TIME
              | dright _ => @None DATE_TIME
              | dbrand _ _ => @None DATE_TIME
              | dforeign f =>
                  match f return (option DATE_TIME) with
                  | enhanceddateTimeformat _ => @None DATE_TIME
                  | enhanceddateTime fd => @Some DATE_TIME fd
                  | enhanceddateTimeduration _ => @None DATE_TIME
                  | enhanceddateTimeperiod _ => @None DATE_TIME
                  end
              end) l)
      =@lift_map (@data enhanced_foreign_data) DATE_TIME
        (fun d0 : @data enhanced_foreign_data =>
         match d0 return (option DATE_TIME) with
         | dunit => @None DATE_TIME
         | dnat _ => @None DATE_TIME
         | dfloat _ => @None DATE_TIME
         | dbool _ => @None DATE_TIME
         | dstring _ => @None DATE_TIME
         | dcoll _ => @None DATE_TIME
         | drec _ => @None DATE_TIME
         | dleft _ => @None DATE_TIME
         | dright _ => @None DATE_TIME
         | dbrand _ _ => @None DATE_TIME
         | dforeign f =>
             match f return (option DATE_TIME) with
             | enhanceddateTimeformat _ => @None DATE_TIME
             | enhanceddateTime fd => @Some DATE_TIME fd
             | enhanceddateTimeduration _ => @None DATE_TIME
             | enhanceddateTimeperiod _ => @None DATE_TIME
             end
         end) l
    ) by reflexivity.
  unfold enhanced_foreign_data, QcertData.enhanced_foreign_data_obligation_5 in *.
  admit.
Admitted.

Lemma unary_op_to_ejson_correct (uop:enhanced_unary_op) :
  forall br d,
    lift DataToEJson.data_to_ejson (enhanced_unary_op_interp br uop d) =
    enhanced_foreign_ejson_runtime_op_interp (unary_op_to_ejson uop)
                                             [DataToEJson.data_to_ejson d].
Proof.
  intros.
  destruct uop.
  - destruct d; destruct u; simpl; try reflexivity.
  - destruct d; destruct l; simpl; try reflexivity.
  - destruct d; destruct m; simpl; try reflexivity.
    destruct (FLOAT_of_string s); reflexivity.
  - destruct d; destruct d0; simpl; try reflexivity; unfold lift;
      try (destruct f; simpl; try reflexivity).
    + rewrite <- ejson_lifted_dbag_comm.
      induction l; simpl in *; try reflexivity.
      unfold onddateTimeList, lift in *; simpl in *.
      unfold lift_dateTimeList in *; simpl in *.
      destruct a; try reflexivity;
        destruct f; try reflexivity; unfold lift in *; simpl.
      destruct (lift_map (onddateTime (fun x : DATE_TIME => x)) l); simpl.
      admit.
      admit.
    + rewrite <- ejson_lifted_dbag_comm.
      induction l; simpl in *; try reflexivity.
      unfold onddateTimeList, lift in *; simpl in *.
      unfold lift_dateTimeList in *; simpl in *.
      destruct a; try reflexivity;
        destruct f; try reflexivity; unfold lift in *; simpl.
      destruct (lift_map (onddateTime (fun x : DATE_TIME => x)) l); simpl.
      admit.
      admit.
Admitted.

Definition binary_op_to_ejson (op:enhanced_binary_op) : enhanced_foreign_ejson_runtime_op :=
  match op with
  | enhanced_binary_math_op mop =>
    match mop with
    | bop_math_atan2 => enhanced_ejson_math EJsonRuntimeAtan2
    end
  | enhanced_binary_date_time_op dop =>
    match dop with
    | bop_date_time_format => enhanced_ejson_date_time EJsonRuntimeDateTimeFormat
    | bop_date_time_add => enhanced_ejson_date_time EJsonRuntimeDateTimeAdd
    | bop_date_time_subtract => enhanced_ejson_date_time EJsonRuntimeDateTimeSubtract
    | bop_date_time_add_period => enhanced_ejson_date_time EJsonRuntimeDateTimeAddPeriod
    | bop_date_time_subtract_period => enhanced_ejson_date_time EJsonRuntimeDateTimeSubtractPeriod
    | bop_date_time_is_same => enhanced_ejson_date_time EJsonRuntimeDateTimeIsSame
    | bop_date_time_is_before => enhanced_ejson_date_time EJsonRuntimeDateTimeIsBefore
    | bop_date_time_is_after => enhanced_ejson_date_time EJsonRuntimeDateTimeIsAfter
    | bop_date_time_diff => enhanced_ejson_date_time EJsonRuntimeDateTimeDiff
    end
  end.

Lemma binary_op_to_ejson_correct (bop:enhanced_binary_op) :
  forall br d1 d2,
    lift DataToEJson.data_to_ejson (enhanced_binary_op_interp br bop d1 d2) =
    enhanced_foreign_ejson_runtime_op_interp (binary_op_to_ejson bop)
                                             [DataToEJson.data_to_ejson d1;DataToEJson.data_to_ejson d2].
Proof.
  intros; destruct bop.
  - destruct m; simpl;
      destruct d1; destruct d2; try reflexivity;
        destruct f; simpl; try reflexivity;
          destruct f0; try reflexivity.
  - destruct d; simpl;
      destruct d1; destruct d2; try reflexivity;
        destruct f; simpl; try reflexivity;
          destruct f0; try reflexivity.
Qed.

Program Instance enhanced_foreign_to_ejson_runtime : foreign_to_ejson_runtime :=
  mk_foreign_to_ejson_runtime
    enhanced_foreign_runtime
    enhanced_foreign_ejson
    enhanced_foreign_to_ejson
    enhanced_foreign_ejson_runtime
    _ _ _ _ _ _.
Next Obligation.
  exact (unary_op_to_ejson uop).
Defined.
Next Obligation.
  apply unary_op_to_ejson_correct.
Defined.
Next Obligation.
  exact (binary_op_to_ejson bop).
Defined.
Next Obligation.
  apply binary_op_to_ejson_correct.
Defined.
(* XXX TODO *)
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
