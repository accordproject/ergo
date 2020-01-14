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

Require Import String.
Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import Equivalence.
Require Import Qcert.Utils.Utils.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.Translation.Operators.ForeignToJava.
Require Import Qcert.Java.JavaRuntime.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

(** Defines the foreign support for DateTime. Posits axioms for the
   basic data/operators, and defines how they are extracted to ocaml
   (using helper functions defined in DateTime.ml) *)

(** Axioms *)
(** A format description for date&time *)
Axiom DATE_TIME_FORMAT : Set.
Extract Constant DATE_TIME_FORMAT => "DateTime.date_time_format".

Axiom DATE_TIME_FORMAT_eq : DATE_TIME_FORMAT -> DATE_TIME_FORMAT -> bool.
Extract Inlined Constant DATE_TIME_FORMAT_eq => "(fun x y -> DateTime.format_eq x y)".

Conjecture DATE_TIME_FORMAT_eq_correct :
  forall f1 f2, (DATE_TIME_FORMAT_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_FORMAT_to_string : DATE_TIME_FORMAT -> string.
Extract Inlined Constant DATE_TIME_FORMAT_to_string => "(fun x -> Util.char_list_of_string (DateTime.format_to_string x))".

Axiom DATE_TIME_FORMAT_from_string : string -> DATE_TIME_FORMAT.
Extract Inlined Constant DATE_TIME_FORMAT_from_string => "(fun x -> DateTime.format_from_string (Util.string_of_char_list x))".

(** A duration *)
Axiom DATE_TIME_DURATION : Set.
Extract Constant DATE_TIME_DURATION => "DateTime.duration".

Axiom DATE_TIME_DURATION_eq : DATE_TIME_DURATION -> DATE_TIME_DURATION -> bool.
Extract Inlined Constant DATE_TIME_DURATION_eq => "(fun x y -> DateTime.duration_eq x y)".

Conjecture DATE_TIME_DURATION_eq_correct :
  forall f1 f2, (DATE_TIME_DURATION_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_DURATION_to_string : DATE_TIME_DURATION -> string.
Extract Inlined Constant DATE_TIME_DURATION_to_string => "(fun x -> Util.char_list_of_string (DateTime.duration_to_string x))".

Axiom DATE_TIME_DURATION_from_string : string -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_string => "(fun x -> DateTime.duration_from_string (Util.string_of_char_list x))".

Axiom DATE_TIME_DURATION_amount : DATE_TIME_DURATION -> Z.
Extract Inlined Constant DATE_TIME_DURATION_amount => "(fun x -> DateTime.duration_amount x)".

(** A time period *)
Axiom DATE_TIME_PERIOD : Set.
Extract Constant DATE_TIME_PERIOD => "DateTime.period".

Axiom DATE_TIME_PERIOD_eq : DATE_TIME_PERIOD -> DATE_TIME_PERIOD -> bool.
Extract Inlined Constant DATE_TIME_PERIOD_eq => "(fun x y -> DateTime.period_eq x y)".

Conjecture DATE_TIME_PERIOD_eq_correct :
  forall f1 f2, (DATE_TIME_PERIOD_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_PERIOD_to_string : DATE_TIME_PERIOD -> string.
Extract Inlined Constant DATE_TIME_PERIOD_to_string => "(fun x -> Util.char_list_of_string (DateTime.period_to_string x))".

Axiom DATE_TIME_PERIOD_from_string : string -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_string => "(fun x -> DateTime.period_from_string (Util.string_of_char_list x))".

(** A date&time *)
Axiom DATE_TIME : Set.
Extract Constant DATE_TIME => "DateTime.dateTime".

Axiom DATE_TIME_now : DATE_TIME.
Extract Inlined Constant DATE_TIME_now => "(DateTime.now ())".

Axiom DATE_TIME_eq : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_eq => "(fun x y -> DateTime.eq x y)".

Conjecture DATE_TIME_eq_correct :
  forall f1 f2, (DATE_TIME_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_format : DATE_TIME -> DATE_TIME_FORMAT -> string.
Extract Inlined Constant DATE_TIME_format => "(fun x f -> Util.char_list_of_string (DateTime.to_string_format x f))".

Axiom DATE_TIME_from_string : string -> DATE_TIME.
Extract Inlined Constant DATE_TIME_from_string => "(fun x -> DateTime.from_string (Util.string_of_char_list x))".

Axiom DATE_TIME_to_string : DATE_TIME -> string.
Extract Inlined Constant DATE_TIME_to_string => "(fun x -> Util.char_list_of_string (DateTime.to_string x))".

(** Components of a date and time *)
Axiom DATE_TIME_get_seconds : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_seconds => "(fun x -> DateTime.get_seconds x)".

Axiom DATE_TIME_get_minutes : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_minutes => "(fun x -> DateTime.get_minutes x)".

Axiom DATE_TIME_get_hours : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_hours => "(fun x -> DateTime.get_hours x)".

Axiom DATE_TIME_get_days : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_days => "(fun x -> DateTime.get_days x)".

Axiom DATE_TIME_get_weeks : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_weeks => "(fun x -> DateTime.get_weeks x)".

Axiom DATE_TIME_get_months : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_months => "(fun x -> DateTime.get_months x)".
  
Axiom DATE_TIME_get_quarters : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_quarters => "(fun x -> DateTime.get_quarters x)".
  
Axiom DATE_TIME_get_years : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_years => "(fun x -> DateTime.get_years x)".

(** Min/Max for date and time *)
Axiom DATE_TIME_max : list DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_max => "(fun x -> DateTime.max x)".

Axiom DATE_TIME_min : list DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_min => "(fun x -> DateTime.min x)".

(** Construct a duration *)
Axiom DATE_TIME_DURATION_from_seconds : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_seconds => "(fun x -> DateTime.duration_from_seconds x)".
  
Axiom DATE_TIME_DURATION_from_minutes : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_minutes => "(fun x -> DateTime.duration_from_minutes x)".
  
Axiom DATE_TIME_DURATION_from_hours : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_hours => "(fun x -> DateTime.duration_from_hours x)".
  
Axiom DATE_TIME_DURATION_from_days : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_days => "(fun x -> DateTime.duration_from_days x)".

Axiom DATE_TIME_DURATION_from_weeks : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_weeks => "(fun x -> DateTime.duration_from_weeks x)".
  
(** Construct a period *)
Axiom DATE_TIME_PERIOD_from_days : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_days => "(fun x -> DateTime.period_from_days x)".
  
Axiom DATE_TIME_PERIOD_from_weeks : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_weeks => "(fun x -> DateTime.period_from_weeks x)".
  
Axiom DATE_TIME_PERIOD_from_months : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_months => "(fun x -> DateTime.period_from_months x)".
  
Axiom DATE_TIME_PERIOD_from_quarters : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_quarters => "(fun x -> DateTime.period_from_quarters x)".
  
Axiom DATE_TIME_PERIOD_from_years : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_years => "(fun x -> DateTime.period_from_years x)".

(** Start of a period *)
Axiom DATE_TIME_start_of_day : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_start_of_day => "(fun x -> DateTime.start_of_day x)".

Axiom DATE_TIME_start_of_month : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_start_of_month => "(fun x -> DateTime.start_of_month x)".

Axiom DATE_TIME_start_of_week : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_start_of_week => "(fun x -> DateTime.start_of_week x)".

Axiom DATE_TIME_start_of_quarter : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_start_of_quarter => "(fun x -> DateTime.start_of_quarter x)".

Axiom DATE_TIME_start_of_year : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_start_of_year => "(fun x -> DateTime.start_of_year x)".

(** End of a period *)
Axiom DATE_TIME_end_of_day : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_end_of_day => "(fun x -> DateTime.end_of_day x)".

Axiom DATE_TIME_end_of_week : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_end_of_week => "(fun x -> DateTime.end_of_week x)".

Axiom DATE_TIME_end_of_month : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_end_of_month => "(fun x -> DateTime.end_of_month x)".

Axiom DATE_TIME_end_of_quarter : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_end_of_quarter => "(fun x -> DateTime.end_of_quarter x)".

Axiom DATE_TIME_end_of_year : DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_end_of_year => "(fun x -> DateTime.end_of_year x)".

(** Arithmetics *)
Axiom DATE_TIME_add : DATE_TIME -> DATE_TIME_DURATION -> DATE_TIME.
Extract Inlined Constant DATE_TIME_add => "(fun x y -> DateTime.add x y)".

Axiom DATE_TIME_subtract : DATE_TIME -> DATE_TIME_DURATION -> DATE_TIME.
Extract Inlined Constant DATE_TIME_subtract => "(fun x y ->  DateTime.subtract x y)".

Axiom DATE_TIME_is_before : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_is_before => "(fun x y -> DateTime.is_before x y)".

Axiom DATE_TIME_is_after : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_is_after => "(fun x y -> DateTime.is_after x y)".

Axiom DATE_TIME_diff : DATE_TIME -> DATE_TIME -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_diff => "(fun x y -> DateTime.diff x y)".

Axiom DATE_TIME_add_period : DATE_TIME -> DATE_TIME_PERIOD -> DATE_TIME.
Extract Inlined Constant DATE_TIME_add_period => "(fun x y -> DateTime.add_period x y)".

Axiom DATE_TIME_subtract_period : DATE_TIME -> DATE_TIME_PERIOD -> DATE_TIME.
Extract Inlined Constant DATE_TIME_subtract_period => "(fun x y ->  DateTime.subtract_period x y)".

Section DateTimeModel.
  (** Equality *)
  Section Equality.
    Program Instance date_time_format_foreign_data : foreign_data
      := {foreign_data_model := DATE_TIME_FORMAT}.
    Next Obligation.
      intros x y.
      case_eq (DATE_TIME_FORMAT_eq x y); intros eqq.
      + left.
        f_equal.
        apply DATE_TIME_FORMAT_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply DATE_TIME_FORMAT_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros f.
      exact (DATE_TIME_FORMAT_to_string f).
    Defined.

    Program Instance date_time_duration_foreign_data : foreign_data
      := {foreign_data_model := DATE_TIME_DURATION}.
    Next Obligation.
      intros x y.
      case_eq (DATE_TIME_DURATION_eq x y); intros eqq.
      + left.
        f_equal.
        apply DATE_TIME_DURATION_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply DATE_TIME_DURATION_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros f.
      exact (DATE_TIME_DURATION_to_string f).
    Defined.

    Program Instance date_time_period_foreign_data : foreign_data
      := {foreign_data_model := DATE_TIME_PERIOD}.
    Next Obligation.
      intros x y.
      case_eq (DATE_TIME_PERIOD_eq x y); intros eqq.
      + left.
        f_equal.
        apply DATE_TIME_PERIOD_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply DATE_TIME_PERIOD_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros f.
      exact (DATE_TIME_PERIOD_to_string f).
    Defined.

    Program Instance date_time_foreign_data : foreign_data
      := {foreign_data_model := DATE_TIME}.
    Next Obligation.
      intros x y.
      case_eq (DATE_TIME_eq x y); intros eqq.
      + left.
        f_equal.
        apply DATE_TIME_eq_correct in eqq.
        trivial.
      + right; intros eqq2.
        red in eqq2.
        apply DATE_TIME_eq_correct in eqq2. 
        congruence.
    Defined.
    Next Obligation.
      exact True.
    Defined.
    Next Obligation.
      reflexivity.
    Qed.
    Next Obligation.
      constructor.
      intros d.
      exact (DATE_TIME_format d (DATE_TIME_FORMAT_from_string "MM/DD/YYYY")).
    Defined.

  End Equality.
  
  Section toString.
    Global Instance date_time_format_to_string : ToString DATE_TIME_FORMAT
      := { toString := DATE_TIME_FORMAT_to_string }.

  End toString.

End DateTimeModel.

Section DateTimeOperators.
  (** Unary operators *)
  Inductive date_time_unary_op :=
  | uop_date_time_get_seconds
  | uop_date_time_get_minutes
  | uop_date_time_get_hours
  | uop_date_time_get_days
  | uop_date_time_get_weeks
  | uop_date_time_get_months
  | uop_date_time_get_quarters
  | uop_date_time_get_years
  | uop_date_time_start_of_day
  | uop_date_time_start_of_week
  | uop_date_time_start_of_month
  | uop_date_time_start_of_quarter
  | uop_date_time_start_of_year
  | uop_date_time_end_of_day
  | uop_date_time_end_of_week
  | uop_date_time_end_of_month
  | uop_date_time_end_of_quarter
  | uop_date_time_end_of_year
  | uop_date_time_format_from_string
  | uop_date_time_from_string
  | uop_date_time_max
  | uop_date_time_min
  | uop_date_time_duration_amount
  | uop_date_time_duration_from_string
  | uop_date_time_duration_from_seconds
  | uop_date_time_duration_from_minutes
  | uop_date_time_duration_from_hours
  | uop_date_time_duration_from_days
  | uop_date_time_duration_from_weeks
  | uop_date_time_period_from_string
  | uop_date_time_period_from_days
  | uop_date_time_period_from_weeks
  | uop_date_time_period_from_months
  | uop_date_time_period_from_quarters
  | uop_date_time_period_from_years
  .

  (** Binary operators *)
  Inductive date_time_binary_op :=
  | bop_date_time_format
  | bop_date_time_add
  | bop_date_time_subtract
  | bop_date_time_add_period
  | bop_date_time_subtract_period
  | bop_date_time_is_same
  | bop_date_time_is_before
  | bop_date_time_is_after
  | bop_date_time_diff
  .

  Section toString.
    Definition date_time_unary_op_tostring (f:date_time_unary_op) : string :=
      match f with
      | uop_date_time_get_seconds => "dateTimeGetSeconds"
      | uop_date_time_get_minutes => "dateTimeGetMinutes"
      | uop_date_time_get_hours => "dateTimeGetHours"
      | uop_date_time_get_days => "dateTimeGetDays"
      | uop_date_time_get_weeks => "dateTimeGetWeeks"
      | uop_date_time_get_months => "dateTimeGetMonths"
      | uop_date_time_get_quarters => "dateTimeGetQuarters"
      | uop_date_time_get_years => "dateTimeGetYears"
      | uop_date_time_start_of_day => "dateTimeStartOf"
      | uop_date_time_start_of_week => "dateTimeStartOf"
      | uop_date_time_start_of_month => "dateTimeStartOf"
      | uop_date_time_start_of_quarter => "dateTimeStartOf"
      | uop_date_time_start_of_year => "dateTimeStartOf"
      | uop_date_time_end_of_day => "dateTimeEndOfDay"
      | uop_date_time_end_of_week => "dateTimeEndOfWeek"
      | uop_date_time_end_of_month => "dateTimeEndOfMonth"
      | uop_date_time_end_of_quarter => "dateTimeEndOfQuarter"
      | uop_date_time_end_of_year => "dateTimeEndOfYears"
      | uop_date_time_format_from_string => "dateTimeFormatFromString"
      | uop_date_time_from_string => "DateTimeFromString"
      | uop_date_time_max => "dateTimeMax"
      | uop_date_time_min => "dateTimeMin"
      | uop_date_time_duration_amount => "dateTimeDurationAmount"
      | uop_date_time_duration_from_string => "dateTimeDurationFromString"
      | uop_date_time_duration_from_seconds => "dateTimeDurationFromSeconds"
      | uop_date_time_duration_from_minutes => "dateTimeDurationFromMinutes"
      | uop_date_time_duration_from_hours => "dateTimeDurationFromHours"
      | uop_date_time_duration_from_days => "dateTimeDurationFromDays"
      | uop_date_time_duration_from_weeks => "dateTimeDurationFromWeeks"
      | uop_date_time_period_from_string => "dateTimePeriodFromString"
      | uop_date_time_period_from_days => "dateTimePeriodFromDays"
      | uop_date_time_period_from_weeks => "dateTimePeriodFromWeeks"
      | uop_date_time_period_from_months => "dateTimePeriodFromMonths"
      | uop_date_time_period_from_quarters => "dateTimePeriodFromQuarters"
      | uop_date_time_period_from_years => "dateTimePeriodFromYears"
      end.

    Definition date_time_binary_op_tostring (f:date_time_binary_op) : string :=
      match f with
      | bop_date_time_format => "dateTimeFormat"
      | bop_date_time_add => "dateTimeAdd"
      | bop_date_time_subtract => "dateTimeSubtract"
      | bop_date_time_add_period => "dateTimeAddPeriod"
      | bop_date_time_subtract_period => "dateTimeSubtractPeriod"
      | bop_date_time_is_same => "dateTimeIsSame"
      | bop_date_time_is_before => "dateTimeIsBefore"
      | bop_date_time_is_after => "dateTimeIsAfter"
      | bop_date_time_diff => "dateTimeDiff"
      end.

  End toString.

  Section toJava.
    Definition cname : nstring := ^"DateTimeComponent".

    Definition date_time_format_to_java_string (f:DATE_TIME_FORMAT) : nstring :=
      cname +++ ^".format(" +++ ^DATE_TIME_FORMAT_to_string f +++ ^")".

    Definition date_time_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:date_time_unary_op)
               (d:java_json) : java_json :=
      match fu with
      | uop_date_time_get_seconds => mk_java_unary_op0_foreign cname (^"date_time_get_seconds") d
      | uop_date_time_get_minutes => mk_java_unary_op0_foreign cname (^"date_time_get_minutes") d
      | uop_date_time_get_hours => mk_java_unary_op0_foreign cname (^"date_time_get_hours") d
      | uop_date_time_get_days => mk_java_unary_op0_foreign cname (^"date_time_get_days") d
      | uop_date_time_get_weeks => mk_java_unary_op0_foreign cname (^"date_time_get_weeks") d
      | uop_date_time_get_months => mk_java_unary_op0_foreign cname (^"date_time_get_months") d
      | uop_date_time_get_quarters => mk_java_unary_op0_foreign cname (^"date_time_get_years") d
      | uop_date_time_get_years => mk_java_unary_op0_foreign cname (^"date_time_get_quarters") d
      | uop_date_time_start_of_day => mk_java_unary_op0_foreign cname (^"date_time_start_of_day") d
      | uop_date_time_start_of_week => mk_java_unary_op0_foreign cname (^"date_time_start_of_week") d
      | uop_date_time_start_of_month => mk_java_unary_op0_foreign cname (^"date_time_start_of_month") d
      | uop_date_time_start_of_quarter => mk_java_unary_op0_foreign cname (^"date_time_start_of_quarter") d
      | uop_date_time_start_of_year => mk_java_unary_op0_foreign cname (^"date_time_start_of_year") d
      | uop_date_time_end_of_day => mk_java_unary_op0_foreign cname (^"date_time_end_of_day") d
      | uop_date_time_end_of_week => mk_java_unary_op0_foreign cname (^"date_time_end_of_week") d
      | uop_date_time_end_of_month => mk_java_unary_op0_foreign cname (^"date_time_end_of_month") d
      | uop_date_time_end_of_quarter => mk_java_unary_op0_foreign cname (^"date_time_end_of_quarter") d
      | uop_date_time_end_of_year => mk_java_unary_op0_foreign cname (^"date_time_end_of_year") d
      | uop_date_time_format_from_string => mk_java_unary_op0_foreign cname (^"date_time_format_from_string") d
      | uop_date_time_from_string => mk_java_unary_op0_foreign cname (^"date_time_from_string") d
      | uop_date_time_max => mk_java_unary_op0_foreign cname (^"date_time_max") d
      | uop_date_time_min => mk_java_unary_op0_foreign cname (^"date_time_min") d
      | uop_date_time_duration_amount => mk_java_unary_op0_foreign cname (^"date_time_duration_amount") d
      | uop_date_time_duration_from_string => mk_java_unary_op0_foreign cname (^"date_time_duration_from_string") d
      | uop_date_time_duration_from_seconds => mk_java_unary_op0_foreign cname (^"date_time_duration_from_seconds") d
      | uop_date_time_duration_from_minutes => mk_java_unary_op0_foreign cname (^"date_time_duration_from_minutes") d
      | uop_date_time_duration_from_hours => mk_java_unary_op0_foreign cname (^"date_time_duration_from_hours") d
      | uop_date_time_duration_from_days => mk_java_unary_op0_foreign cname (^"date_time_duration_from_days") d
      | uop_date_time_duration_from_weeks => mk_java_unary_op0_foreign cname (^"date_time_duration_from_weeks") d
      | uop_date_time_period_from_string => mk_java_unary_op0 (^"date_time_period_from_string") d
      | uop_date_time_period_from_days => mk_java_unary_op0_foreign cname (^"date_time_period_from_days") d
      | uop_date_time_period_from_weeks => mk_java_unary_op0_foreign cname (^"date_time_period_from_weeks") d
      | uop_date_time_period_from_months => mk_java_unary_op0_foreign cname (^"date_time_period_from_months") d
      | uop_date_time_period_from_quarters => mk_java_unary_op0_foreign cname (^"date_time_period_from_quarters") d
      | uop_date_time_period_from_years => mk_java_unary_op0_foreign cname (^"date_time_period_from_years") d
      end.

    Definition date_time_to_java_binary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fb:date_time_binary_op)
               (d1 d2:java_json) : java_json :=
      match fb with
      | bop_date_time_format => mk_java_binary_op0_foreign cname (^"date_time_format") d1 d2
      | bop_date_time_add => mk_java_binary_op0_foreign cname (^"date_time_add") d1 d2
      | bop_date_time_subtract => mk_java_binary_op0_foreign cname (^"date_time_subtract") d1 d2
      | bop_date_time_add_period => mk_java_binary_op0_foreign cname (^"date_time_add_period") d1 d2
      | bop_date_time_subtract_period => mk_java_binary_op0_foreign cname (^"date_time_subtract_perid") d1 d2
      | bop_date_time_is_same =>  mk_java_binary_op0_foreign cname (^"date_time_is_same") d1 d2
      | bop_date_time_is_before =>  mk_java_binary_op0_foreign cname (^"date_time_is_before") d1 d2
      | bop_date_time_is_after =>  mk_java_binary_op0_foreign cname (^"date_time_is_after") d1 d2
      | bop_date_time_diff => mk_java_binary_op0_foreign cname (^"date_time_diff") d1 d2
      end.

  End toJava.

  Section toEJson.
    Inductive ejson_date_time_runtime_op :=
    (* Unary *)
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
    (* Binary *)
    | EJsonRuntimeDateTimeFormat
    | EJsonRuntimeDateTimeAdd
    | EJsonRuntimeDateTimeSubtract
    | EJsonRuntimeDateTimeAddPeriod
    | EJsonRuntimeDateTimeSubtractPeriod
    | EJsonRuntimeDateTimeIsSame
    | EJsonRuntimeDateTimeIsBefore
    | EJsonRuntimeDateTimeIsAfter
    | EJsonRuntimeDateTimeDiff
    .

    Definition ejson_date_time_runtime_op_tostring op : string :=
      match op with
      (* Unary *)
      | EJsonRuntimeDateTimeGetSeconds => "dateTimeGetSeconds"
      | EJsonRuntimeDateTimeGetMinutes => "dateTimeGetMinutes"
      | EJsonRuntimeDateTimeGetHours => "dateTimeGetHours"
      | EJsonRuntimeDateTimeGetDays => "dateTimeGetDays"
      | EJsonRuntimeDateTimeGetWeeks => "dateTimeGetWeeks"
      | EJsonRuntimeDateTimeGetMonths => "dateTimeGetMonths"
      | EJsonRuntimeDateTimeGetQuarters => "dateTimeGetQuarters"
      | EJsonRuntimeDateTimeGetYears => "dateTimeGetYears"
      | EJsonRuntimeDateTimeStartOfDay => "dateTimeStartOfDay"
      | EJsonRuntimeDateTimeStartOfWeek => "dateTimeStartOfWeek"
      | EJsonRuntimeDateTimeStartOfMonth => "dateTimeStartOfMonth"
      | EJsonRuntimeDateTimeStartOfQuarter => "dateTimeStartOfQuarter"
      | EJsonRuntimeDateTimeStartOfYear => "dateTimeStartOfYear"
      | EJsonRuntimeDateTimeEndOfDay => "dateTimeEndOfDay"
      | EJsonRuntimeDateTimeEndOfWeek => "dateTimeEndOfWeek"
      | EJsonRuntimeDateTimeEndOfMonth => "dateTimeEndOfMonth"
      | EJsonRuntimeDateTimeEndOfQuarter => "dateTimeEndOfQuarter"
      | EJsonRuntimeDateTimeEndOfYear => "dateTimeEndOfYear"
      | EJsonRuntimeDateTimeFormatFromString => "dateTimeFormatFromString"
      | EJsonRuntimeDateTimeFromString => "dateTimeFromString"
      | EJsonRuntimeDateTimeMax => "dateTimeMax"
      | EJsonRuntimeDateTimeMin => "dateTimeMin"
      | EJsonRuntimeDateTimeDurationAmount => "dateTimeDurationAmount"
      | EJsonRuntimeDateTimeDurationFromString => "dateTimeDurationFromString"
      | EJsonRuntimeDateTimePeriodFromString => "dateTimePeriodFromString"
      | EJsonRuntimeDateTimeDurationFromSeconds => "dateTimeDurationFromSeconds"
      | EJsonRuntimeDateTimeDurationFromMinutes => "dateTimeDurationFromMinutes"
      | EJsonRuntimeDateTimeDurationFromHours => "dateTimeDurationFromHours"
      | EJsonRuntimeDateTimeDurationFromDays => "dateTimeDurationFromDays"
      | EJsonRuntimeDateTimeDurationFromWeeks => "dateTimeDurationFromWeeks"
      | EJsonRuntimeDateTimePeriodFromDays => "dateTimePeriodFromDays"
      | EJsonRuntimeDateTimePeriodFromWeeks => "dateTimePeriodFromWeeks"
      | EJsonRuntimeDateTimePeriodFromMonths => "dateTimePeriodFromMonths"
      | EJsonRuntimeDateTimePeriodFromQuarters => "dateTimePeriodFromQuarters"
      | EJsonRuntimeDateTimePeriodFromYears => "dateTimePeriodFromYears"
      (* Binary *)
      | EJsonRuntimeDateTimeFormat => "dateTimeFormat"
      | EJsonRuntimeDateTimeAdd => "dateTimeAdd"
      | EJsonRuntimeDateTimeSubtract => "dateTimeSubtract"
      | EJsonRuntimeDateTimeAddPeriod => "dateTimeAddPeriod"
      | EJsonRuntimeDateTimeSubtractPeriod => "dateTimeSubtractPeriod"
      | EJsonRuntimeDateTimeIsSame => "dateTimeIsSame"
      | EJsonRuntimeDateTimeIsBefore => "dateTimeIsBefore"
      | EJsonRuntimeDateTimeIsAfter => "dateTimeIsAfter"
      | EJsonRuntimeDateTimeDiff => "dateTimeDiff"
      end.

  End toEJson.
  
End DateTimeOperators.
