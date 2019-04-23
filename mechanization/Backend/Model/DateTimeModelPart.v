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
Require Import Qcert.Common.DataModel.ForeignData.
Require Import Qcert.Common.Operators.ForeignOperators.
Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Translation.ForeignToJava.
Require Import Qcert.Translation.NNRCtoJava.

Import ListNotations.
Local Open Scope string.

(** Defines the foreign support for DateTime
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/ocaml/...../Util.ml)
     *)

(* First we define a DATE_TIME_FORMAT *)

Axiom DATE_TIME_FORMAT : Set.
Extract Constant DATE_TIME_FORMAT => "DateTime.date_time_format".

Axiom DATE_TIME_FORMAT_eq : DATE_TIME_FORMAT -> DATE_TIME_FORMAT -> bool.
Extract Inlined Constant DATE_TIME_FORMAT_eq => "(fun x y -> DateTime.format_eq x y)".

Conjecture DATE_TIME_FORMAT_eq_correct :
  forall f1 f2, (DATE_TIME_FORMAT_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_FORMAT_to_string : DATE_TIME_FORMAT -> String.string.
Extract Inlined Constant DATE_TIME_FORMAT_to_string => "(fun x -> Util.char_list_of_string (DateTime.format_to_string x))".

Axiom DATE_TIME_FORMAT_from_string : String.string -> DATE_TIME_FORMAT.
Extract Inlined Constant DATE_TIME_FORMAT_from_string => "(fun x -> DateTime.format_from_string (Util.string_of_char_list x))".

Program Instance date_time_format_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME_FORMAT}.
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

Global Instance date_time_format_to_string : ToString DATE_TIME_FORMAT
  := { toString := DATE_TIME_FORMAT_to_string }.

(* First we define a DATE_TIME_DURATION *)

Axiom DATE_TIME_DURATION : Set.
Extract Constant DATE_TIME_DURATION => "DateTime.duration".

Axiom DATE_TIME_DURATION_eq : DATE_TIME_DURATION -> DATE_TIME_DURATION -> bool.
Extract Inlined Constant DATE_TIME_DURATION_eq => "(fun x y -> DateTime.duration_eq x y)".

Conjecture DATE_TIME_DURATION_eq_correct :
  forall f1 f2, (DATE_TIME_DURATION_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_DURATION_to_string : DATE_TIME_DURATION -> String.string.
Extract Inlined Constant DATE_TIME_DURATION_to_string => "(fun x -> Util.char_list_of_string (DateTime.duration_to_string x))".

Axiom DATE_TIME_DURATION_from_string : String.string -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_string => "(fun x -> DateTime.duration_from_string (Util.string_of_char_list x))".

Axiom DATE_TIME_DURATION_amount : DATE_TIME_DURATION -> Z.
Extract Inlined Constant DATE_TIME_DURATION_amount => "(fun x -> DateTime.duration_amount x)".

Program Instance date_time_duration_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME_DURATION}.
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

Inductive date_time_duration_unit :=
| date_time_duration_SECONDS
| date_time_duration_MINUTES
| date_time_duration_HOURS
| date_time_duration_DAYS
| date_time_duration_WEEKS.

Definition date_time_duration_unit_tostring (part:date_time_duration_unit) : String.string :=
  match part with
  | date_time_duration_SECONDS => "SECONDS"
  | date_time_duration_MINUTES => "MINUTES"
  | date_time_duration_HOURS => "HOURS"
  | date_time_duration_DAYS => "DAYS"
  | date_time_duration_WEEKS => "WEEKS"
  end.

Global Instance date_time_duration_unit_to_string : ToString date_time_duration_unit
  := { toString := date_time_duration_unit_tostring }.

(* Second we define a DATE_TIME_PERIOD *)

Axiom DATE_TIME_PERIOD : Set.
Extract Constant DATE_TIME_PERIOD => "DateTime.period".

Axiom DATE_TIME_PERIOD_eq : DATE_TIME_PERIOD -> DATE_TIME_PERIOD -> bool.
Extract Inlined Constant DATE_TIME_PERIOD_eq => "(fun x y -> DateTime.period_eq x y)".

Conjecture DATE_TIME_PERIOD_eq_correct :
  forall f1 f2, (DATE_TIME_PERIOD_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_PERIOD_to_string : DATE_TIME_PERIOD -> String.string.
Extract Inlined Constant DATE_TIME_PERIOD_to_string => "(fun x -> Util.char_list_of_string (DateTime.period_to_string x))".

Axiom DATE_TIME_PERIOD_from_string : String.string -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_from_string => "(fun x -> DateTime.period_from_string (Util.string_of_char_list x))".

Program Instance date_time_period_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME_PERIOD}.
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

Inductive date_time_period_unit :=
| date_time_period_DAYS
| date_time_period_WEEKS
| date_time_period_MONTHS
| date_time_period_QUARTERS
| date_time_period_YEARS.

Definition date_time_period_unit_tostring (part:date_time_period_unit) : String.string :=
  match part with
  | date_time_period_DAYS => "DAYS"
  | date_time_period_WEEKS => "WEEKS"
  | date_time_period_MONTHS => "MONTHS"
  | date_time_period_QUARTERS => "QUARTERS"
  | date_time_period_YEARS => "YEARS"
  end.

Global Instance date_time_period_unit_to_string : ToString date_time_period_unit
  := { toString := date_time_period_unit_tostring }.

(* Now we define a DATE_TIME. *)

Axiom DATE_TIME : Set.
Extract Constant DATE_TIME => "DateTime.dateTime".

Axiom DATE_TIME_now : DATE_TIME.
Extract Inlined Constant DATE_TIME_now => "(DateTime.now ())".

Axiom DATE_TIME_eq : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_eq => "(fun x y -> DateTime.eq x y)".

Conjecture DATE_TIME_eq_correct :
  forall f1 f2, (DATE_TIME_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_format : DATE_TIME -> DATE_TIME_FORMAT -> String.string.
Extract Inlined Constant DATE_TIME_format => "(fun x f -> Util.char_list_of_string (DateTime.to_string_format x f))".

Axiom DATE_TIME_from_string : String.string -> DATE_TIME.
Extract Inlined Constant DATE_TIME_from_string => "(fun x -> DateTime.from_string (Util.string_of_char_list x))".

Program Instance date_time_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME}.
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

Inductive date_time_component :=
| date_time_component_SECONDS
| date_time_component_MINUTES
| date_time_component_HOURS
| date_time_component_DAYS
| date_time_component_WEEKS
| date_time_component_MONTHS
| date_time_component_QUARTERS
| date_time_component_YEARS.

Definition date_time_component_tostring (part:date_time_component) : String.string :=
  match part with
  | date_time_component_SECONDS => "SECONDS"
  | date_time_component_MINUTES => "MINUTES"
  | date_time_component_HOURS => "HOURS"
  | date_time_component_DAYS => "DAYS"
  | date_time_component_WEEKS => "WEEKS"
  | date_time_component_MONTHS => "MONTHS"
  | date_time_component_QUARTERS => "QUARTERS"
  | date_time_component_YEARS => "YEARS"
  end.

Global Instance date_time_component_to_string : ToString date_time_component
  := { toString := date_time_component_tostring }.

(* Accesses components of a date and time *)
Axiom DATE_TIME_get_second : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_second => "(fun x -> DateTime.get_second x)".

Axiom DATE_TIME_get_minute : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_minute => "(fun x -> DateTime.get_minute x)".

Axiom DATE_TIME_get_hour : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_hour => "(fun x -> DateTime.get_hour x)".

Axiom DATE_TIME_get_day : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_day => "(fun x -> DateTime.get_day x)".

Axiom DATE_TIME_get_week : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_week => "(fun x -> DateTime.get_week x)".
  
Axiom DATE_TIME_get_month : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_month => "(fun x -> DateTime.get_month x)".
  
Axiom DATE_TIME_get_quarter : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_quarter => "(fun x -> DateTime.get_quarter x)".
  
Axiom DATE_TIME_get_year : DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_get_year => "(fun x -> DateTime.get_year x)".

(* Max/Min for date and time *)
Axiom DATE_TIME_max : list DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_max => "(fun x -> DateTime.max x)".

Axiom DATE_TIME_min : list DATE_TIME -> DATE_TIME.
Extract Inlined Constant DATE_TIME_min => "(fun x -> DateTime.min x)".

(* Construct a duration *)
Axiom DATE_TIME_DURATION_seconds : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_seconds => "(fun x -> DateTime.duration_seconds x)".
  
Axiom DATE_TIME_DURATION_minutes : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_minutes => "(fun x -> DateTime.duration_minutes x)".
  
Axiom DATE_TIME_DURATION_hours : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_hours => "(fun x -> DateTime.duration_hours x)".
  
Axiom DATE_TIME_DURATION_days : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_days => "(fun x -> DateTime.duration_days x)".
  
Axiom DATE_TIME_DURATION_weeks : Z -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_weeks => "(fun x -> DateTime.duration_weeks x)".
  
(* Construct a period *)
Axiom DATE_TIME_PERIOD_days : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_days => "(fun x -> DateTime.period_days x)".
  
Axiom DATE_TIME_PERIOD_weeks : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_weeks => "(fun x -> DateTime.period_weeks x)".
  
Axiom DATE_TIME_PERIOD_months : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_months => "(fun x -> DateTime.period_months x)".
  
Axiom DATE_TIME_PERIOD_quarters : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_quarters => "(fun x -> DateTime.period_quarters x)".
  
Axiom DATE_TIME_PERIOD_years : Z -> DATE_TIME_PERIOD.
Extract Inlined Constant DATE_TIME_PERIOD_years => "(fun x -> DateTime.period_years x)".

(* Start of a period *)
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

(* End of a period *)
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

(* DateTime components *)
Definition DATE_TIME_component (part:date_time_component) (dt:DATE_TIME) : Z :=
  match part with
  | date_time_component_SECONDS => DATE_TIME_get_second dt
  | date_time_component_MINUTES => DATE_TIME_get_minute dt
  | date_time_component_HOURS => DATE_TIME_get_hour dt
  | date_time_component_DAYS => DATE_TIME_get_day dt
  | date_time_component_WEEKS => DATE_TIME_get_week dt
  | date_time_component_MONTHS => DATE_TIME_get_month dt
  | date_time_component_QUARTERS => DATE_TIME_get_quarter dt
  | date_time_component_YEARS => DATE_TIME_get_year dt
  end.

(* Duration from Z *)
Definition DATE_TIME_DURATION_from_nat (part:date_time_duration_unit) (z:Z) : DATE_TIME_DURATION :=
  match part with
  | date_time_duration_SECONDS => DATE_TIME_DURATION_seconds z
  | date_time_duration_MINUTES => DATE_TIME_DURATION_minutes z
  | date_time_duration_HOURS => DATE_TIME_DURATION_hours z
  | date_time_duration_DAYS => DATE_TIME_DURATION_days z
  | date_time_duration_WEEKS => DATE_TIME_DURATION_weeks z
  end.

(* Period from Z *)
Definition DATE_TIME_PERIOD_from_nat (part:date_time_period_unit) (z:Z) : DATE_TIME_PERIOD :=
  match part with
  | date_time_period_DAYS => DATE_TIME_PERIOD_days z
  | date_time_period_WEEKS => DATE_TIME_PERIOD_weeks z
  | date_time_period_MONTHS => DATE_TIME_PERIOD_months z
  | date_time_period_QUARTERS => DATE_TIME_PERIOD_quarters z
  | date_time_period_YEARS => DATE_TIME_PERIOD_years z
  end.

Definition DATE_TIME_start_of (part:date_time_period_unit) (dt:DATE_TIME) : DATE_TIME :=
  match part with
  | date_time_period_DAYS => DATE_TIME_start_of_day dt
  | date_time_period_WEEKS => DATE_TIME_start_of_week dt
  | date_time_period_MONTHS => DATE_TIME_start_of_month dt
  | date_time_period_QUARTERS => DATE_TIME_start_of_quarter dt
  | date_time_period_YEARS => DATE_TIME_start_of_year dt
  end.

Definition DATE_TIME_end_of (part:date_time_period_unit) (dt:DATE_TIME) : DATE_TIME :=
  match part with
  | date_time_period_DAYS => DATE_TIME_end_of_day dt
  | date_time_period_WEEKS => DATE_TIME_end_of_week dt
  | date_time_period_MONTHS => DATE_TIME_end_of_month dt
  | date_time_period_QUARTERS => DATE_TIME_end_of_quarter dt
  | date_time_period_YEARS => DATE_TIME_end_of_year dt
  end.

Inductive date_time_unary_op :=
| uop_date_time_component : date_time_component -> date_time_unary_op
| uop_date_time_start_of : date_time_period_unit -> date_time_unary_op
| uop_date_time_end_of : date_time_period_unit -> date_time_unary_op
| uop_date_time_format_from_string : date_time_unary_op
| uop_date_time_from_string
| uop_date_time_max
| uop_date_time_min
| uop_date_time_duration_amount
| uop_date_time_duration_from_string
| uop_date_time_duration_from_nat : date_time_duration_unit -> date_time_unary_op
| uop_date_time_period_from_string
| uop_date_time_period_from_nat : date_time_period_unit -> date_time_unary_op
.

Definition date_time_unary_op_tostring (f:date_time_unary_op) : String.string :=
  match f with
  | uop_date_time_component part =>
    "(dateTimeComponent" ++ (date_time_component_tostring part) ++ ")"
  | uop_date_time_start_of part =>
    "(dateTimeStartOf" ++ (date_time_period_unit_tostring part) ++ ")"
  | uop_date_time_end_of part =>
    "(dateTimeEndOf" ++ (date_time_period_unit_tostring part) ++ ")"
  | uop_date_time_format_from_string => "dateTimeFormatFromString"
  | uop_date_time_from_string => "DateTimeFromString"
  | uop_date_time_max => "DateTimeMax"
  | uop_date_time_min => "DateTimeMin"
  | uop_date_time_duration_amount => "DateTimeDurationAmount"
  | uop_date_time_duration_from_string => "DateTimeDurationFromString"
  | uop_date_time_duration_from_nat part =>
    "(DateTimeDurationFromNat" ++ (date_time_duration_unit_tostring part) ++ ")"
  | uop_date_time_period_from_string => "DateTimePeriodFromString"
  | uop_date_time_period_from_nat part =>
    "(DateTimePeriodFromNat" ++ (date_time_period_unit_tostring part) ++ ")"
  end.

Definition date_time_component_to_java_string (part:date_time_component): string :=
  match part with
  | date_time_component_SECONDS => "UnaryOperators.seconds"
  | date_time_component_MINUTES => "UnaryOperators.minutes"
  | date_time_component_HOURS => "UnaryOperators.hours"
  | date_time_component_DAYS => "UnaryOperators.days"
  | date_time_component_WEEKS => "UnaryOperators.weeks"
  | date_time_component_MONTHS => "UnaryOperators.months"
  | date_time_component_QUARTERS => "UnaryOperators.quarters"
  | date_time_component_YEARS => "UnaryOperators.years"
  end.

Definition date_time_duration_unit_to_java_string (part:date_time_duration_unit) : string :=
  match part with
  | date_time_duration_SECONDS => "UnaryOperators.seconds"
  | date_time_duration_MINUTES => "UnaryOperators.minutes"
  | date_time_duration_HOURS => "UnaryOperators.hours"
  | date_time_duration_DAYS => "UnaryOperators.days"
  | date_time_duration_WEEKS => "UnaryOperators.weeks"
  end.

Definition date_time_period_unit_to_java_string (part:date_time_period_unit) : string :=
  match part with
  | date_time_period_DAYS => "UnaryOperators.days"
  | date_time_period_WEEKS => "UnaryOperators.weeks"
  | date_time_period_MONTHS => "UnaryOperators.months"
  | date_time_period_QUARTERS => "UnaryOperators.quarters"
  | date_time_period_YEARS => "UnaryOperators.years"
  end.

Definition date_time_format_to_java_string (f:DATE_TIME_FORMAT) : string :=
  "UnaryOperators.format(" ++ DATE_TIME_FORMAT_to_string f ++ ")".

Definition date_time_to_java_unary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fu:date_time_unary_op)
           (d:java_json) : java_json :=
  match fu with
  | uop_date_time_component part =>
    mk_java_unary_op1 "date_time_component" (date_time_component_to_java_string part) d
  | uop_date_time_start_of part =>
    mk_java_unary_op1 "date_time_start_of" (date_time_period_unit_to_java_string part) d
  | uop_date_time_end_of part =>
    mk_java_unary_op1 "date_time_end_of" (date_time_period_unit_to_java_string part) d
  | uop_date_time_format_from_string => mk_java_unary_op0 "date_time_format_from_string" d
  | uop_date_time_from_string => mk_java_unary_op0 "date_time_from_string" d
  | uop_date_time_max => mk_java_unary_op0 "date_time_max" d
  | uop_date_time_min => mk_java_unary_op0 "date_time_min" d
  | uop_date_time_duration_amount => mk_java_unary_op0 "date_time_duration_amount" d
  | uop_date_time_duration_from_string => mk_java_unary_op0 "date_time_duration_from_string" d
  | uop_date_time_duration_from_nat part =>
    mk_java_unary_op1 "date_time_duration_from_nat" (date_time_duration_unit_to_java_string part) d
  | uop_date_time_period_from_string => mk_java_unary_op0 "date_time_period_from_string" d
  | uop_date_time_period_from_nat part =>
    mk_java_unary_op1 "date_time_period_from_nat" (date_time_period_unit_to_java_string part) d
  end.

Definition date_time_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:date_time_unary_op)
             (d:String.string) : String.string :=
  match fu with
  | uop_date_time_component part => "dateTimeComponent(" ++ (toString part) ++ ", " ++ d ++ ")"
  | uop_date_time_start_of part => "dateTimeStartOf(" ++ (toString part) ++ ", " ++ d ++ ")"
  | uop_date_time_end_of part => "dateTimeEndOf(" ++ (toString part) ++ ", " ++ d ++ ")"
  | uop_date_time_format_from_string => "dateTimeFormatFromString(" ++ d ++ ")"
  | uop_date_time_from_string => "dateTimeFromString(" ++ d ++ ")"
  | uop_date_time_max => "dateTimeMax(" ++ d ++ ")"
  | uop_date_time_min => "dateTimeMin(" ++ d ++ ")"
  | uop_date_time_duration_amount => "dateTimeDurationAmount(" ++ d ++ ")"
  | uop_date_time_duration_from_string => "dateTimeDurationFromString(" ++ d ++ ")"
  | uop_date_time_duration_from_nat part => "dateTimeDurationFromNat(" ++ (toString part) ++ ", " ++ d ++ ")"
  | uop_date_time_period_from_string => "dateTimePeriodFromString(" ++ d ++ ")"
  | uop_date_time_period_from_nat part => "dateTimePeriodFromNat(" ++ (toString part) ++ ", " ++ d ++ ")"
  end.

Definition date_time_to_ajavascript_unary_op
             (fu:date_time_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | uop_date_time_component part =>
       call_runtime "dateTimeComponent" [ expr_literal (literal_string (toString part)); e ]
     | uop_date_time_start_of part =>
       call_runtime "dateTimeStartOf" [ expr_literal (literal_string (toString part)); e ]
     | uop_date_time_end_of part =>
       call_runtime "dateTimeEndOf" [ expr_literal (literal_string (toString part)); e ]
     | uop_date_time_format_from_string => call_runtime "dateTimeFormatFromString" [ e ]
     | uop_date_time_from_string => call_runtime "dateTimeFromString" [ e ]
     | uop_date_time_max => call_runtime "dateTimeMax" [ e ]
     | uop_date_time_min => call_runtime "dateTimeMin" [ e ]
     | uop_date_time_duration_amount => call_runtime "dateTimeDurationAmount" [ e ]
     | uop_date_time_duration_from_string => call_runtime "dateTimeDurationFromString" [ e ]
     | uop_date_time_duration_from_nat part =>
       call_runtime "dateTimeDurationFromNat" [ expr_literal (literal_string (toString part)); e ]
     | uop_date_time_period_from_string => call_runtime "dateTimePeriodFromString" [ e ]
     | uop_date_time_period_from_nat part =>
       call_runtime "dateTimePeriodFromNat" [ expr_literal (literal_string (toString part)); e ]
     end.

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

Definition date_time_binary_op_tostring (f:date_time_binary_op) : String.string
  := match f with
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

(* Java equivalent: JavaScriptBackend.jsFunc *)
Definition jsFunc (name d1 d2:string)
  := name ++ "(" ++ d1 ++ ", " ++ d2 ++ ")".

Definition date_time_to_java_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:date_time_binary_op)
             (d1 d2:java_json) : java_json
  := match fb with
     | bop_date_time_format => mk_java_binary_op0 "date_time_format" d1 d2
     | bop_date_time_add => mk_java_binary_op0 "date_time_add" d1 d2
     | bop_date_time_subtract => mk_java_binary_op0 "date_time_subtract" d1 d2
     | bop_date_time_add_period => mk_java_binary_op0 "date_time_add_period" d1 d2
     | bop_date_time_subtract_period => mk_java_binary_op0 "date_time_subtract_perid" d1 d2
     | bop_date_time_is_same =>  mk_java_binary_op0 "date_time_is_same" d1 d2
     | bop_date_time_is_before =>  mk_java_binary_op0 "date_time_is_before" d1 d2
     | bop_date_time_is_after =>  mk_java_binary_op0 "date_time_is_after" d1 d2
     | bop_date_time_diff => mk_java_binary_op0 "date_time_diff" d1 d2
     end.

Definition date_time_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:date_time_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_date_time_format => jsFunc "dateTimeFormat" d1 d2
     | bop_date_time_add => jsFunc "dateTimeAdd" d1 d2
     | bop_date_time_subtract => jsFunc "dateTimeSubtract" d1 d2
     | bop_date_time_add_period => jsFunc "dateTimeAddPeriod" d1 d2
     | bop_date_time_subtract_period => jsFunc "dateTimeSubtractPeriod" d1 d2
     | bop_date_time_is_same =>  jsFunc "dateTimeIsSame" d1 d2
     | bop_date_time_is_before =>  jsFunc "dateTimeIsBefore" d1 d2
     | bop_date_time_is_after =>  jsFunc "dateTimeIsAfter" d1 d2
     | bop_date_time_diff => jsFunc "dateTimeDiff" d1 d2
     end.

Definition date_time_to_ajavascript_binary_op
             (fb:date_time_binary_op)
             (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | bop_date_time_format => call_runtime "dateTimeFormat" [ e1; e2 ]
     | bop_date_time_add => call_runtime "dateTimeAdd" [ e1; e2 ]
     | bop_date_time_subtract => call_runtime "dateTimeSubtract" [ e1; e2 ]
     | bop_date_time_add_period => call_runtime "dateTimeAddPeriod" [ e1; e2 ]
     | bop_date_time_subtract_period => call_runtime "dateTimeSubtractPeriod" [ e1; e2 ]
     | bop_date_time_is_same =>  call_runtime "dateTimeIsSame" [ e1; e2 ]
     | bop_date_time_is_before =>  call_runtime "dateTimeIsBefore" [ e1; e2 ]
     | bop_date_time_is_after =>  call_runtime "dateTimeIsAfter" [ e1; e2 ]
     | bop_date_time_diff => call_runtime "dateTimeDiff" [ e1; e2 ]
     end.  

