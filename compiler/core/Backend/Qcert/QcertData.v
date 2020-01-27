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
Require Import Qcert.Data.DataSystem.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Import ListNotations.
Local Open Scope list_scope.

Inductive enhanced_data : Set
  :=
  | enhanceddateTimeformat : DATE_TIME_FORMAT -> enhanced_data
  | enhanceddateTime : DATE_TIME -> enhanced_data
  | enhanceddateTimeduration : DATE_TIME_DURATION -> enhanced_data
  | enhanceddateTimeperiod : DATE_TIME_PERIOD -> enhanced_data
.

Definition enhanceddateTime_now := DATE_TIME_now.

Existing Instance date_time_format_foreign_data.
Existing Instance date_time_foreign_data.
Existing Instance date_time_duration_foreign_data.
Existing Instance date_time_period_foreign_data.

Program Instance enhanced_foreign_data : foreign_data
  := mk_foreign_data enhanced_data _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_format_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_duration_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_period_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact True.
  - exact (@foreign_data_normalized date_time_foreign_data d).
  - exact (@foreign_data_normalized date_time_duration_foreign_data d).
  - exact (@foreign_data_normalized date_time_period_foreign_data d).
Defined.
Next Obligation.
  destruct a.
  - simpl; trivial.
  - exact (@foreign_data_normalize_normalizes date_time_foreign_data d).
  - exact (@foreign_data_normalize_normalizes date_time_duration_foreign_data d).
  - exact (@foreign_data_normalize_normalizes date_time_period_foreign_data d).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring date_time_format_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_duration_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_period_foreign_data) d).
Defined.

Definition denhanceddateTimeformat td := dforeign (enhanceddateTimeformat td).
Definition denhanceddateTime td := dforeign (enhanceddateTime td).
Definition denhanceddateTimeduration td := dforeign (enhanceddateTimeduration td).
Definition denhanceddateTimeperiod td := dforeign (enhanceddateTimeperiod td).

Inductive enhanced_unary_op :=
| enhanced_unary_uri_op : uri_unary_op -> enhanced_unary_op
| enhanced_unary_log_op : log_unary_op -> enhanced_unary_op
| enhanced_unary_math_op : math_unary_op -> enhanced_unary_op
| enhanced_unary_date_time_op : date_time_unary_op -> enhanced_unary_op
.

Definition onddateTime {A} (f : DATE_TIME -> A) (d : data) : option A :=
  match d with
  | dforeign (enhanceddateTime fd) => Some (f fd)
  | _ => None
  end.

Definition lift_dateTimeList (l:list data) : option (list DATE_TIME) :=
  lift_map
    (fun d =>
       match d with
       | dforeign (enhanceddateTime fd) => Some fd
       | _ => None
       end) l.

Definition onddateTimeList (f : list DATE_TIME -> DATE_TIME) (d : data) : option DATE_TIME :=
  let odates :=
      match d with
      | dcoll c => lift_dateTimeList c
      | _ => None
      end
  in
  lift f odates.

Definition onddateTimeduration {A} (f : DATE_TIME_DURATION -> A) (d : data) : option A :=
  match d with
  | dforeign (enhanceddateTimeduration fd) => Some (f fd)
  | _ => None
  end.

Definition onddateTimeDurationNat {A} (f : Z -> A) (d : data) : option A :=
  match d with
  | dnat z => Some (f z)
  | _ => None
  end.

Definition onddateTimePeriodNat {A} (f : Z -> A) (d : data) : option A :=
  match d with
  | dnat z => Some (f z)
  | _ => None
  end.

Definition ondstring {A} (f : String.string -> A) (d : data) : option A :=
  match d with
  | dstring s => Some (f s)
  | _ => None
  end.

Definition ondstringfloatopt (f : String.string -> option float) (d : data) : option data :=
  match d with
  | dstring s =>
    match f s with
    | None => Some dnone
    | Some n => Some (dsome (dfloat n))
    end
  | _ => None
  end.

Definition ondstringunit (f : String.string -> unit) (d : data) : option data :=
  match d with
  | dstring s =>
    match f s with                                           (* Call log *)
    | y => if unit_eqdec y tt then Some dunit else None      (* Return unit *)
    end
  | _ => None
  end.

Definition ondstringstring (f : String.string -> string) (d : data) : option data :=
  match d with
  | dstring s =>
    Some (dstring (f s))
  | _ => None
  end.

Definition ondfloat {A} (f : float -> A) (d : data) : option A :=
  match d with
  | dfloat s => Some (f s)
  | _ => None
  end.

Definition uri_unary_op_interp (op:uri_unary_op) (d:data) : option data :=
  match op with
  | uop_uri_encode => ondstringstring URI_encode d
  | uop_uri_decode => ondstringstring URI_decode d
  end.

Definition log_unary_op_interp (op:log_unary_op) (d:data) : option data :=
  match op with
  | uop_log_string => ondstringunit LOG_string d
  end.

Definition math_unary_op_interp (op:math_unary_op) (d:data) : option data :=
  match op with
  | uop_math_float_of_string => ondstringfloatopt FLOAT_of_string d
  | uop_math_acos => lift dfloat (ondfloat FLOAT_acos d)
  | uop_math_asin => lift dfloat (ondfloat FLOAT_asin d)
  | uop_math_atan => lift dfloat (ondfloat FLOAT_atan d)
  | uop_math_cos => lift dfloat (ondfloat FLOAT_cos d)
  | uop_math_cosh => lift dfloat (ondfloat FLOAT_cosh d)
  | uop_math_sin => lift dfloat (ondfloat FLOAT_sin d)
  | uop_math_sinh => lift dfloat (ondfloat FLOAT_sinh d)
  | uop_math_tan => lift dfloat (ondfloat FLOAT_tan d)
  | uop_math_tanh => lift dfloat (ondfloat FLOAT_tanh d)
  end.

Definition date_time_unary_op_interp (op:date_time_unary_op) (d:data) : option data :=
  match op with
  | uop_date_time_get_seconds =>
    lift dnat (onddateTime DATE_TIME_get_seconds d)
  | uop_date_time_get_minutes =>
    lift dnat (onddateTime DATE_TIME_get_minutes d)
  | uop_date_time_get_hours =>
    lift dnat (onddateTime DATE_TIME_get_hours d)
  | uop_date_time_get_days =>
    lift dnat (onddateTime DATE_TIME_get_days d)
  | uop_date_time_get_weeks =>
    lift dnat (onddateTime DATE_TIME_get_weeks d)
  | uop_date_time_get_months =>
    lift dnat (onddateTime DATE_TIME_get_months d)
  | uop_date_time_get_quarters =>
    lift dnat (onddateTime DATE_TIME_get_quarters d)
  | uop_date_time_get_years =>
    lift dnat (onddateTime DATE_TIME_get_years d)
  | uop_date_time_start_of_day =>
    lift denhanceddateTime (onddateTime DATE_TIME_start_of_day d)
  | uop_date_time_start_of_week =>
    lift denhanceddateTime (onddateTime DATE_TIME_start_of_week d)
  | uop_date_time_start_of_month =>
    lift denhanceddateTime (onddateTime DATE_TIME_start_of_month d)
  | uop_date_time_start_of_quarter =>
    lift denhanceddateTime (onddateTime DATE_TIME_start_of_quarter d)
  | uop_date_time_start_of_year =>
    lift denhanceddateTime (onddateTime DATE_TIME_start_of_year d)
  | uop_date_time_end_of_day =>
    lift denhanceddateTime (onddateTime DATE_TIME_end_of_day d)
  | uop_date_time_end_of_week =>
    lift denhanceddateTime (onddateTime DATE_TIME_end_of_week d)
  | uop_date_time_end_of_month =>
    lift denhanceddateTime (onddateTime DATE_TIME_end_of_month d)
  | uop_date_time_end_of_quarter =>
    lift denhanceddateTime (onddateTime DATE_TIME_end_of_quarter d)
  | uop_date_time_end_of_year =>
    lift denhanceddateTime (onddateTime DATE_TIME_end_of_year d)
  | uop_date_time_format_from_string =>
    lift denhanceddateTimeformat (ondstring DATE_TIME_FORMAT_from_string d)
  | uop_date_time_from_string =>
    lift denhanceddateTime (ondstring DATE_TIME_from_string d)
  | uop_date_time_max =>
    lift denhanceddateTime (onddateTimeList DATE_TIME_max d)
  | uop_date_time_min =>
    lift denhanceddateTime (onddateTimeList DATE_TIME_min d)
  | uop_date_time_duration_amount =>
    lift dnat (onddateTimeduration DATE_TIME_DURATION_amount d)
  | uop_date_time_duration_from_string =>
    lift denhanceddateTimeduration (ondstring DATE_TIME_DURATION_from_string d)
  | uop_date_time_duration_from_seconds =>
    lift denhanceddateTimeduration (onddateTimeDurationNat DATE_TIME_DURATION_from_seconds d)
  | uop_date_time_duration_from_minutes =>
    lift denhanceddateTimeduration (onddateTimeDurationNat DATE_TIME_DURATION_from_minutes d)
  | uop_date_time_duration_from_hours =>
    lift denhanceddateTimeduration (onddateTimeDurationNat DATE_TIME_DURATION_from_hours d)
  | uop_date_time_duration_from_days =>
    lift denhanceddateTimeduration (onddateTimeDurationNat DATE_TIME_DURATION_from_days d)
  | uop_date_time_duration_from_weeks =>
    lift denhanceddateTimeduration (onddateTimeDurationNat DATE_TIME_DURATION_from_weeks d)
  | uop_date_time_period_from_string =>
    lift denhanceddateTimeperiod (ondstring DATE_TIME_PERIOD_from_string d)
  | uop_date_time_period_from_days =>
    lift denhanceddateTimeperiod (onddateTimePeriodNat DATE_TIME_PERIOD_from_days d)
  | uop_date_time_period_from_weeks =>
    lift denhanceddateTimeperiod (onddateTimePeriodNat DATE_TIME_PERIOD_from_weeks d)
  | uop_date_time_period_from_months =>
    lift denhanceddateTimeperiod (onddateTimePeriodNat DATE_TIME_PERIOD_from_months d)
  | uop_date_time_period_from_quarters =>
    lift denhanceddateTimeperiod (onddateTimePeriodNat DATE_TIME_PERIOD_from_quarters d)
  | uop_date_time_period_from_years =>
    lift denhanceddateTimeperiod (onddateTimePeriodNat DATE_TIME_PERIOD_from_years d)
  end.

Definition enhanced_unary_op_interp
           (br:brand_relation_t)
           (op:enhanced_unary_op)
           (d:data) : option data :=
  match op with
  | enhanced_unary_uri_op f => uri_unary_op_interp f d
  | enhanced_unary_log_op f => log_unary_op_interp f d
  | enhanced_unary_math_op f => math_unary_op_interp f d
  | enhanced_unary_date_time_op f => date_time_unary_op_interp f d
  end.

Section toString. (* XXX Maybe to move as a component ? *)
  Fixpoint enumToString (b:brands) (d:data) : string :=
    match d with
    | dleft (dstring s) =>
      append "~"
             (append (@toString _ ToString_brands b)
                     (append "."
                             (stringToString s)))
    | dright d => enumToString b d
    | _ => "<BOGUS ENUM>"
    end.

  Fixpoint dataToString (d:data) : string :=
    match d with
    | dunit => "unit"%string
    | dnat n => toString n
    | dfloat n => toString n
    | dbool b => toString b
    | dstring s => string_bracket """"%string (stringToString s) """"%string
    | dcoll l => string_bracket
                   "["%string
                   (concat ", "
                           (map dataToString l))
                   "]"%string
    | drec lsd => string_bracket
                    "{"%string
                    (concat "," 
                            (map (fun xy => let '(x,y):=xy in 
                                            (append (stringToString x) (append ":"%string
                                                                               (dataToString y)))
                                 ) lsd))
                    "}"%string
    | dleft d => string_bracket
                   "Left("%string
                   (dataToString d)
                   ")"%string
    | dright d => string_bracket
                    "Right("%string
                    (dataToString d)
                    ")"%string
    | dbrand b d =>
      match d with
      | drec _ =>
        append "~"
               (append (@toString _ ToString_brands b)
                       (dataToString d))
      | dleft _
      | dright _ =>
        enumToString b d
      | _ =>
         "<BOGUS OBJECT>"
      end
    | dforeign fd => toString fd
    end.

  Definition dataToText (d:data) : string := dataToString d.
End toString.

Inductive enhanced_binary_op :=
| enhanced_binary_math_op : math_binary_op -> enhanced_binary_op
| enhanced_binary_date_time_op : date_time_binary_op -> enhanced_binary_op
.

Definition ondfloat2 {A} (f : float -> float -> A) (d1 d2 : data) : option A :=
  match d1, d2 with
  | dfloat fd1, dfloat fd2 => Some (f fd1 fd2)
  | _, _ => None
  end.

Definition onddateTime2 {A} (f : DATE_TIME -> DATE_TIME -> A) (d1 d2 : data) : option A :=
  match d1, d2 with
  | dforeign (enhanceddateTime fd1), dforeign (enhanceddateTime fd2) => Some (f fd1 fd2)
  | _, _ => None
  end.

Definition rondbooldateTime2 (f: DATE_TIME -> DATE_TIME -> bool) (d1 d2:data) : option data :=
  lift dbool (onddateTime2 f d1 d2).

Definition math_binary_op_interp
           (op:math_binary_op) (d1 d2:data) : option data :=
  match op with
  | bop_math_atan2 => lift dfloat (ondfloat2 FLOAT_atan2 d1 d2)
  end.

Definition date_time_binary_op_interp
           (op:date_time_binary_op) (d1 d2:data) : option data :=
  match op with
  | bop_date_time_format
    => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeformat td)
         => Some (dstring (DATE_TIME_format tp td))
       | _,_ => None
       end
  | bop_date_time_add
    => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeduration td)
         => Some (denhanceddateTime (DATE_TIME_add tp td))
       | _,_ => None
       end
  | bop_date_time_subtract
    => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeduration td)
         => Some (denhanceddateTime (DATE_TIME_subtract tp td))
       | _,_ => None
       end
  | bop_date_time_add_period
    => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeperiod td)
         => Some (denhanceddateTime (DATE_TIME_add_period tp td))
       | _,_ => None
       end
  | bop_date_time_subtract_period
    => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeperiod td)
         => Some (denhanceddateTime (DATE_TIME_subtract_period tp td))
       | _,_ => None
       end
  | bop_date_time_is_same => rondbooldateTime2 DATE_TIME_eq d1 d2
  | bop_date_time_is_before => rondbooldateTime2 DATE_TIME_is_before d1 d2
  | bop_date_time_is_after => rondbooldateTime2 DATE_TIME_is_after d1 d2
  | bop_date_time_diff => lift denhanceddateTimeduration (onddateTime2 DATE_TIME_diff d1 d2)
  end.

Definition enhanced_binary_op_interp
           (br:brand_relation_t)
           (op:enhanced_binary_op)
           (d1 d2:data) : option data :=
  match op with
  | enhanced_binary_math_op f => math_binary_op_interp f d1 d2
  | enhanced_binary_date_time_op f => date_time_binary_op_interp f d1 d2
  end.

Program Instance enhanced_foreign_operators : foreign_operators
  := { foreign_operators_unary := enhanced_unary_op
       ; foreign_operators_unary_interp := enhanced_unary_op_interp
       ; foreign_operators_unary_data_tostring := dataToString
       ; foreign_operators_unary_data_totext := dataToText
       ; foreign_operators_binary := enhanced_binary_op
       ; foreign_operators_binary_interp := enhanced_binary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  repeat (decide equality).
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (uri_unary_op_tostring u).
  - exact (log_unary_op_tostring l).
  - exact (math_unary_op_tostring m).
  - exact (date_time_unary_op_tostring d).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct u; simpl in H; unfold ondstringunit, lift in H; simpl in H;
      destruct d; simpl in H; try discriminate; invcs H; repeat constructor.
  - destruct l; simpl in H; unfold ondstringunit, lift in H; simpl in H;
      destruct d; simpl in H; try discriminate; invcs H; repeat constructor.
  - destruct m; simpl in H; unfold ondstring, ondfloat, lift in H; simpl in H;
      destruct d; simpl in H; try discriminate; invcs H; repeat constructor.
    destruct (FLOAT_of_string s); try discriminate; invcs H2; repeat constructor.
  - destruct d0; simpl in H;
      unfold onddateTime, onddateTimeList, onddateTimeduration,
      denhanceddateTime, denhanceddateTimeduration,
      denhanceddateTimeperiod, lift in H;
      simpl in H;
      destruct d; simpl in H; try discriminate; try (try (destruct f); invcs H; repeat constructor).
    + case_eq (match lift_dateTimeList l with
            | Some a' => Some (DATE_TIME_max a')
            | None => None
            end); intros;
        rewrite H in H2.
      inversion H2.
      invcs H3; repeat constructor.
      congruence.
    + case_eq (match lift_dateTimeList l with
            | Some a' => Some (DATE_TIME_min a')
            | None => None
            end); intros;
        rewrite H in H2.
      inversion H2.
      invcs H3; repeat constructor.
      congruence.
Defined.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  repeat (decide equality).
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (math_binary_op_tostring m).
  - exact (date_time_binary_op_tostring d).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct m; simpl in H;
      unfold ondfloat2, lift in H
      ; destruct d1; simpl in H; try discriminate
      ; destruct f; simpl in H; try discriminate
      ; destruct d2; simpl in H; try discriminate
      ; try (destruct f; simpl in H; try discriminate)
      ; invcs H
      ; repeat constructor.
  - destruct d; simpl in H;
      unfold rondbooldateTime2, onddateTime2, denhanceddateTime, lift in H
      ; destruct d1; simpl in H; try discriminate
      ; destruct f; simpl in H; try discriminate
      ; destruct d2; simpl in H; try discriminate
      ; try (destruct f; simpl in H; try discriminate)
      ; invcs H
      ; repeat constructor.
Defined.

Instance enhanced_foreign_runtime :
  foreign_runtime
  := mk_foreign_runtime
       enhanced_foreign_data
       enhanced_foreign_operators.

