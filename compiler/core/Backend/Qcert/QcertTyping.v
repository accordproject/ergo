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

Require Import QcertData.
Require Import QcertEJson.
Require Import QcertDataToEJson.
Require Import QcertEJsonToJSON.
Require Import QcertToJava.
Require Import QcertToJavascriptAst.
Require Import QcertReduceOps.
Require Import QcertToReduceOps.
Require Import QcertToSpark.
Require Import QcertType.
Require Import QcertToScala.
Require Import QcertDataTyping.
Require Import QcertTypeToJSON.
Require Import QcertRuntime.

Definition DateTimeFormat {br:brand_relation} : rtype := Foreign enhancedDateTimeFormat.
Definition DateTime {br:brand_relation} : rtype := Foreign enhancedDateTime.
Definition DateTimeDuration {br:brand_relation} : rtype := Foreign enhancedDateTimeDuration.
Definition DateTimePeriod {br:brand_relation} : rtype := Foreign enhancedDateTimePeriod.

Definition isDateTimeFormat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTimeFormat => true
  | _ => false
  end.

Definition isDateTime {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTime => true
  | _ => false
  end.

Definition isDateTimeDuration {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTimeDuration => true
  | _ => false
  end.

Definition isDateTimePeriod {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTimePeriod => true
  | _ => false
  end.

Definition isNat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Nat₀ => true
  | _ => false
  end.

Definition isString {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | String₀ => true
  | _ => false
  end.

Definition isFloat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Float₀ => true
  | _ => false
  end.

Definition tuncoll {model:brand_model} (τ:rtype) : option rtype.
Proof.
  destruct τ.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
  - exact None.
  - exact None.
  - exact None.
  - exact None.
  - exact None.
Defined.

Inductive uri_unary_op_has_type {model:brand_model} :
  uri_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_uri_encode_string : uri_unary_op_has_type uop_uri_encode RType.String RType.String
  | tuop_uri_decode_string : uri_unary_op_has_type uop_uri_decode RType.String RType.String.

Inductive log_unary_op_has_type {model:brand_model} :
  log_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_log_string : log_unary_op_has_type uop_log_string RType.String Unit.

Inductive math_unary_op_has_type {model:brand_model} :
  math_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_math_float_of_string : math_unary_op_has_type uop_math_float_of_string RType.String (Option Float)
  | tuop_math_acos : math_unary_op_has_type uop_math_acos Float Float
  | tuop_math_asin : math_unary_op_has_type uop_math_asin Float Float
  | tuop_math_atan : math_unary_op_has_type uop_math_atan Float Float
  | tuop_math_cos : math_unary_op_has_type uop_math_cos Float Float
  | tuop_math_cosh : math_unary_op_has_type uop_math_cosh Float Float
  | tuop_math_sin : math_unary_op_has_type uop_math_sin Float Float
  | tuop_math_sinh : math_unary_op_has_type uop_math_sinh Float Float
  | tuop_math_tan : math_unary_op_has_type uop_math_tan Float Float
  | tuop_math_tanh : math_unary_op_has_type uop_math_tanh Float Float.

Inductive date_time_unary_op_has_type {model:brand_model} :
  date_time_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_date_time_get_seconds : date_time_unary_op_has_type uop_date_time_get_seconds DateTime Nat
  | tuop_date_time_get_minutes : date_time_unary_op_has_type uop_date_time_get_minutes DateTime Nat
  | tuop_date_time_get_hours : date_time_unary_op_has_type uop_date_time_get_hours DateTime Nat
  | tuop_date_time_get_days : date_time_unary_op_has_type uop_date_time_get_days DateTime Nat
  | tuop_date_time_get_weeks : date_time_unary_op_has_type uop_date_time_get_weeks DateTime Nat
  | tuop_date_time_get_months : date_time_unary_op_has_type uop_date_time_get_months DateTime Nat
  | tuop_date_time_get_quarters : date_time_unary_op_has_type uop_date_time_get_quarters DateTime Nat
  | tuop_date_time_get_years : date_time_unary_op_has_type uop_date_time_get_years DateTime Nat
  | tuop_date_time_start_of_day : date_time_unary_op_has_type uop_date_time_start_of_day DateTime DateTime
  | tuop_date_time_start_of_week : date_time_unary_op_has_type uop_date_time_start_of_week DateTime DateTime
  | tuop_date_time_start_of_month : date_time_unary_op_has_type uop_date_time_start_of_month DateTime DateTime
  | tuop_date_time_start_of_quarter : date_time_unary_op_has_type uop_date_time_start_of_quarter DateTime DateTime
  | tuop_date_time_start_of_year : date_time_unary_op_has_type uop_date_time_start_of_year DateTime DateTime
  | tuop_date_time_end_of_day : date_time_unary_op_has_type uop_date_time_end_of_day DateTime DateTime
  | tuop_date_time_end_of_week : date_time_unary_op_has_type uop_date_time_end_of_week DateTime DateTime
  | tuop_date_time_end_of_month : date_time_unary_op_has_type uop_date_time_end_of_month DateTime DateTime
  | tuop_date_time_end_of_quarter : date_time_unary_op_has_type uop_date_time_end_of_quarter DateTime DateTime
  | tuop_date_time_end_of_year : date_time_unary_op_has_type uop_date_time_end_of_year DateTime DateTime
  | tuop_date_time_format_from_string : date_time_unary_op_has_type uop_date_time_format_from_string RType.String DateTimeFormat
  | tuop_date_time_from_string : date_time_unary_op_has_type uop_date_time_from_string RType.String DateTime
  | tuop_date_time_max : date_time_unary_op_has_type uop_date_time_max (RType.Coll DateTime) DateTime
  | tuop_date_time_min : date_time_unary_op_has_type uop_date_time_min (RType.Coll DateTime) DateTime
  | tuop_date_time_duration_amount : date_time_unary_op_has_type uop_date_time_duration_amount DateTimeDuration Nat
  | tuop_date_time_duration_from_string : date_time_unary_op_has_type uop_date_time_duration_from_string RType.String DateTimeDuration
  | tuop_date_time_duration_from_seconds : date_time_unary_op_has_type uop_date_time_duration_from_seconds RType.Nat DateTimeDuration
  | tuop_date_time_duration_from_minutes : date_time_unary_op_has_type uop_date_time_duration_from_minutes RType.Nat DateTimeDuration
  | tuop_date_time_duration_from_hours : date_time_unary_op_has_type uop_date_time_duration_from_hours RType.Nat DateTimeDuration
  | tuop_date_time_duration_from_days : date_time_unary_op_has_type uop_date_time_duration_from_days RType.Nat DateTimeDuration
  | tuop_date_time_duration_from_weeks : date_time_unary_op_has_type uop_date_time_duration_from_weeks RType.Nat DateTimeDuration
  | tuop_date_time_period_from_string : date_time_unary_op_has_type uop_date_time_period_from_string RType.String DateTimePeriod
  | tuop_date_time_period_from_days : date_time_unary_op_has_type uop_date_time_period_from_days RType.Nat DateTimePeriod
  | tuop_date_time_period_from_weeks : date_time_unary_op_has_type uop_date_time_period_from_weeks RType.Nat DateTimePeriod
  | tuop_date_time_period_from_months : date_time_unary_op_has_type uop_date_time_period_from_months RType.Nat DateTimePeriod
  | tuop_date_time_period_from_quarters : date_time_unary_op_has_type uop_date_time_period_from_quarters RType.Nat DateTimePeriod
  | tuop_date_time_period_from_years : date_time_unary_op_has_type uop_date_time_period_from_years RType.Nat DateTimePeriod
.

Definition uri_unary_op_type_infer {model : brand_model} (op:uri_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_uri_encode =>
    if isString τ₁ then Some RType.String else None
  | uop_uri_decode =>
    if isString τ₁ then Some RType.String else None
  end.

Definition log_unary_op_type_infer {model : brand_model} (op:log_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_log_string =>
    if isString τ₁ then Some Unit else None
  end.

Definition math_unary_op_type_infer {model : brand_model} (op:math_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_math_float_of_string =>
    if isString τ₁ then Some (Option Float) else None
  | _ =>
    if isFloat τ₁ then Some Float else None
  end.

Definition date_time_unary_op_type_infer {model : brand_model} (op:date_time_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_date_time_get_seconds =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_minutes =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_hours =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_days =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_weeks =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_months =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_quarters =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_get_years =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_start_of_day =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_start_of_week =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_start_of_month =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_start_of_quarter =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_start_of_year =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_end_of_day =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_end_of_week =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_end_of_month =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_end_of_quarter =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_end_of_year =>
    if isDateTime τ₁ then Some DateTime else None
  | uop_date_time_format_from_string =>
    if isString τ₁ then Some DateTimeFormat else None
  | uop_date_time_from_string =>
    if isString τ₁ then Some DateTime else None
  | uop_date_time_max =>
    match tuncoll τ₁ with
    | Some τ₂ => if isDateTime τ₂ then Some DateTime else None
    | None => None
    end
  | uop_date_time_min =>
    match tuncoll τ₁ with
    | Some τ₂ => if isDateTime τ₂ then Some DateTime else None
    | None => None
    end
  | uop_date_time_duration_amount =>
    if isDateTimeDuration τ₁ then Some Nat else None
  | uop_date_time_duration_from_string =>
    if isString τ₁ then Some DateTimeDuration else None
  | uop_date_time_duration_from_seconds =>
    if isNat τ₁ then Some DateTimeDuration else None
  | uop_date_time_duration_from_minutes =>
    if isNat τ₁ then Some DateTimeDuration else None
  | uop_date_time_duration_from_hours =>
    if isNat τ₁ then Some DateTimeDuration else None
  | uop_date_time_duration_from_days =>
    if isNat τ₁ then Some DateTimeDuration else None
  | uop_date_time_duration_from_weeks =>
    if isNat τ₁ then Some DateTimeDuration else None
  | uop_date_time_period_from_string =>
    if isString τ₁ then Some DateTimePeriod else None
  | uop_date_time_period_from_days =>
    if isNat τ₁ then Some DateTimePeriod else None
  | uop_date_time_period_from_weeks =>
    if isNat τ₁ then Some DateTimePeriod else None
  | uop_date_time_period_from_months =>
    if isNat τ₁ then Some DateTimePeriod else None
  | uop_date_time_period_from_quarters =>
    if isNat τ₁ then Some DateTimePeriod else None
  | uop_date_time_period_from_years =>
    if isNat τ₁ then Some DateTimePeriod else None
  end.

Definition uri_unary_op_type_infer_sub {model : brand_model} (op:uri_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_uri_encode =>
    enforce_unary_op_schema (τ₁,RType.String) RType.String
  | uop_uri_decode =>
    enforce_unary_op_schema (τ₁,RType.String) RType.String
  end.

Definition log_unary_op_type_infer_sub {model : brand_model} (op:log_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_log_string =>
    enforce_unary_op_schema (τ₁,RType.String) Unit
  end.

Definition math_unary_op_type_infer_sub {model : brand_model} (op:math_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_math_float_of_string =>
    enforce_unary_op_schema (τ₁,RType.String) (Option Float)
  | _ =>
    enforce_unary_op_schema (τ₁,Float) Float
  end.

Definition date_time_unary_op_type_infer_sub {model : brand_model} (op:date_time_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_date_time_get_seconds =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_minutes =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_hours =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_days =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_weeks =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_months =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_quarters =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_get_years =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_start_of_day =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_start_of_week =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_start_of_month =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_start_of_quarter =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_start_of_year =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_end_of_day =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_end_of_week =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_end_of_month =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_end_of_quarter =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_end_of_year =>
    enforce_unary_op_schema (τ₁,DateTime) DateTime
  | uop_date_time_format_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTimeFormat
  | uop_date_time_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTime
  | uop_date_time_max =>
    enforce_unary_op_schema (τ₁,RType.Coll DateTime) DateTime
  | uop_date_time_min =>
    enforce_unary_op_schema (τ₁,RType.Coll DateTime) DateTime
  | uop_date_time_duration_amount =>
    enforce_unary_op_schema (τ₁,DateTimeDuration) Nat
  | uop_date_time_duration_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTimeDuration
  | uop_date_time_duration_from_seconds =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimeDuration
  | uop_date_time_duration_from_minutes =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimeDuration
  | uop_date_time_duration_from_hours =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimeDuration
  | uop_date_time_duration_from_days =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimeDuration
  | uop_date_time_duration_from_weeks =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimeDuration
  | uop_date_time_period_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTimePeriod
  | uop_date_time_period_from_days =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimePeriod
  | uop_date_time_period_from_weeks =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimePeriod
  | uop_date_time_period_from_months =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimePeriod
  | uop_date_time_period_from_quarters =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimePeriod
  | uop_date_time_period_from_years =>
    enforce_unary_op_schema (τ₁,RType.Nat) DateTimePeriod
  end.

Lemma uri_unary_op_typing_sound {model : brand_model}
      (fu : uri_unary_op) (τin τout : rtype) :
  uri_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      uri_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
Qed.

Lemma log_unary_op_typing_sound {model : brand_model}
      (fu : log_unary_op) (τin τout : rtype) :
  log_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      log_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
Qed.

Lemma math_unary_op_typing_sound {model : brand_model}
      (fu : math_unary_op) (τin τout : rtype) :
  math_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      math_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
  - inversion 1; subst.
    try invcs H0.
    try invcs H.
    simpl; simpl.
    destruct (FLOAT_of_string s).
    eexists; split; try reflexivity; repeat constructor.
    eexists; split; try reflexivity; repeat constructor.
Qed.

Lemma lift_dateTimeList_sound {model : brand_model} (dl:list data) (e:true = true) :
  Forall (fun d : data => d ▹ exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) (Foreign₀ enhancedDateTime) e) dl
  -> exists (dout : list DATE_TIME), lift_dateTimeList dl = Some dout.
Proof.
  revert dl.
  induction dl; intros; simpl in *.
  - eexists; reflexivity.
  - inversion H; clear H; subst.
    inversion H2; clear H2; subst.
    inversion H1; clear H1; subst.
    unfold lift_dateTimeList in *; simpl in *.
    specialize (IHdl H3); clear H3.
    elim IHdl; clear IHdl; intros.
    rewrite H.
    simpl.
    exists (tp :: x).
    reflexivity.
Qed.

Lemma date_time_max_sound {model : brand_model} :
  date_time_unary_op_has_type uop_date_time_max (Coll DateTime) DateTime ->
  forall din : data,
    din ▹ Coll DateTime ->
    exists dout : data, date_time_unary_op_interp uop_date_time_max din = Some dout /\ dout ▹ DateTime.
Proof.
  intro H.
  invcs H; intros;
    inversion H; clear H; subst.
  destruct r; simpl in *; try congruence.
  destruct x; simpl in *; try congruence.
  destruct ft; simpl in *; try congruence.
  clear H0.
  unfold onddateTimeList.
  elim (lift_dateTimeList_sound dl e H2); clear H2 e; intros.
  rewrite H.
  simpl.
  eexists; split; [reflexivity|repeat constructor].
Qed.

Lemma date_time_min_sound {model : brand_model} :
  date_time_unary_op_has_type uop_date_time_min (Coll DateTime) DateTime ->
  forall din : data,
    din ▹ Coll DateTime ->
    exists dout : data, date_time_unary_op_interp uop_date_time_min din = Some dout /\ dout ▹ DateTime.
Proof.
  intro H.
  invcs H; intros;
    inversion H; clear H; subst.
  destruct r; simpl in *; try congruence.
  destruct x; simpl in *; try congruence.
  destruct ft; simpl in *; try congruence.
  clear H0.
  unfold onddateTimeList.
  elim (lift_dateTimeList_sound dl e H2); clear H2 e; intros.
  rewrite H.
  simpl.
  eexists; split; [reflexivity|repeat constructor].
Qed.

Lemma date_time_unary_op_typing_sound {model : brand_model}
      (fu : date_time_unary_op) (τin τout : rtype) :
  date_time_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      date_time_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
              try invcs H0;
              try invcs H3;
              simpl; unfold denhanceddateTime, denhanceddateTimeduration; simpl;
              eexists; split; try reflexivity;
              repeat constructor].
  apply date_time_max_sound; assumption.
  apply date_time_min_sound; assumption.
Qed.

Inductive enhanced_unary_op_has_type {model:brand_model} : enhanced_unary_op -> rtype -> rtype -> Prop
  :=
  | tenhanced_unary_uri_op fu τin τout:
      uri_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_uri_op fu) τin τout
  | tenhanced_unary_log_op fu τin τout:
      log_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_log_op fu) τin τout
  | tenhanced_unary_math_op fu τin τout:
      math_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_math_op fu) τin τout
  | tenhanced_unary_date_time_op fu τin τout:
      date_time_unary_op_has_type fu τin τout ->
      enhanced_unary_op_has_type (enhanced_unary_date_time_op fu) τin τout.

Definition enhanced_unary_op_typing_infer {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option rtype :=
  match fu with
  | enhanced_unary_uri_op op => uri_unary_op_type_infer op τ
  | enhanced_unary_log_op op => log_unary_op_type_infer op τ
  | enhanced_unary_math_op op => math_unary_op_type_infer op τ
  | enhanced_unary_date_time_op op => date_time_unary_op_type_infer op τ
  end.

Lemma enhanced_unary_op_typing_infer_correct
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout ->
  enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            try (rewrite String_canon; constructor);
            rewrite String_canon; constructor.
  - destruct l; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            try (rewrite String_canon; constructor);
            rewrite String_canon; constructor.
  - destruct m; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H; constructor;
            try (rewrite String_canon; constructor);
            rewrite Float_canon; constructor.
  - destruct d; simpl in *;
      try (destruct τ₁; simpl in *; try congruence;
           destruct x; simpl in *; try congruence;
           destruct ft; simpl in *; try congruence;
           inversion H; subst; clear H; constructor;
           rewrite Foreign_canon; constructor);
      try (destruct τ₁; simpl in *; try congruence;
           destruct x; simpl in *; try congruence;
           inversion H; subst; clear H; constructor;
           try (rewrite String_canon; constructor);
           rewrite Float_canon; constructor);
      try (destruct τ₁; simpl in *; try congruence;
           destruct x; simpl in *; try congruence;
           case_eq (isDateTime (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)); intros; rewrite H0 in H; try congruence;
           inversion H; clear H; subst;
           unfold isDateTime in H0;
           destruct x; simpl in *; try congruence;
           destruct ft; simpl in *; try congruence;
           rewrite Coll_canon;
           rewrite Foreign_canon;
           repeat constructor);
      try (destruct τ₁; simpl in *; try congruence;
           destruct x; simpl in *; try congruence;
           inversion H; subst; clear H; constructor;
           rewrite Nat_canon; constructor).
Qed.

Lemma enhanced_unary_op_typing_infer_least
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout₁ τout₂} :
  enhanced_unary_op_typing_infer fu τ₁ = Some τout₁ ->
  enhanced_unary_op_has_type fu τ₁ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H;
            try (rewrite String_canon in H0);
            inversion H0; subst; clear H0;
              inversion H1; subst; clear H1;
                reflexivity.
  - destruct l; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H;
            try (rewrite String_canon in H0);
            inversion H0; subst; clear H0;
              inversion H1; subst; clear H1;
                reflexivity.
  - destruct m; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          inversion H; subst; clear H;
            try (rewrite String_canon in H0);
            try (rewrite Float_canon in H0);
            inversion H0; subst; clear H0;
              inversion H1; subst; clear H1;
                reflexivity.
  - destruct d; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          try (destruct ft; simpl in *; try congruence;
               inversion H; subst; clear H;
               rewrite Foreign_canon in H0;
               inversion H0; subst; clear H0;
               inversion H1; subst; clear H1;
               reflexivity);
          try (inversion H; subst; clear H;
               rewrite String_canon in H0;
               inversion H0; subst; clear H0;
               inversion H1; subst; clear H1;
               reflexivity);
          try (case_eq (isDateTime (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e));
               intros; rewrite H1 in H; try congruence;
               inversion H; subst; clear H;
               unfold isDateTime in H1;
               destruct x; simpl in *; try congruence;
               destruct ft; simpl in *; try congruence;
               rewrite Coll_canon in H0;
               rewrite Foreign_canon in H0;
               clear H1; inversion H0; subst; clear H0; inversion H1; subst; clear H1;
               reflexivity);
          try (inversion H; subst; clear H;
               rewrite Nat_canon in H0;
               inversion H0; subst; clear H0;
               inversion H1; subst; clear H1;
               reflexivity).
Qed.

Lemma enhanced_unary_op_typing_infer_complete
      {model:brand_model}
      (fu:foreign_operators_unary)
      {τ₁ τout} : 
  enhanced_unary_op_typing_infer fu τ₁ = None ->
  ~ enhanced_unary_op_has_type fu τ₁ τout.
Proof.
  intros.
  destruct fu; simpl in *.
  - destruct u; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2; inversion H.
  - destruct l; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2; inversion H.
  - destruct m; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2; inversion H.
  - destruct d; simpl in *;
      destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
          unfold not; intros;
            inversion H0; subst; clear H0;
              inversion H2; subst; clear H2;
                simpl in H; congruence.
Qed.

Definition enhanced_unary_op_typing_infer_sub {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option (rtype*rtype) :=
  match fu with
  | enhanced_unary_uri_op op => uri_unary_op_type_infer_sub op τ
  | enhanced_unary_log_op op => log_unary_op_type_infer_sub op τ
  | enhanced_unary_math_op op => math_unary_op_type_infer_sub op τ
  | enhanced_unary_date_time_op op => date_time_unary_op_type_infer_sub op τ
  end.

Lemma enhanced_unary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_unary) (τin τout : rtype) :
  enhanced_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      enhanced_unary_op_interp brand_relation_brands fu din = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply uri_unary_op_typing_sound; eauto.
  - eapply log_unary_op_typing_sound; eauto.
  - eapply math_unary_op_typing_sound; eauto.
  - eapply date_time_unary_op_typing_sound; eauto.
Qed.

Inductive math_binary_op_has_type {model:brand_model} :
  math_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_math_atan2 :
      math_binary_op_has_type bop_math_atan2 Float Float Float.

Inductive date_time_binary_op_has_type {model:brand_model} :
  date_time_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_date_time_format :
      date_time_binary_op_has_type bop_date_time_format DateTime DateTimeFormat RType.String
  | tbop_date_time_add :
      date_time_binary_op_has_type bop_date_time_add DateTime DateTimeDuration DateTime 
  | tbop_date_time_subtract :
      date_time_binary_op_has_type bop_date_time_subtract DateTime DateTimeDuration DateTime 
  | tbop_date_time_add_period :
      date_time_binary_op_has_type bop_date_time_add_period DateTime DateTimePeriod DateTime 
  | tbop_date_time_subtract_period :
      date_time_binary_op_has_type bop_date_time_subtract_period DateTime DateTimePeriod DateTime 
  | tbop_date_time_is_same :
      date_time_binary_op_has_type bop_date_time_is_same DateTime DateTime Bool 
  | tbop_date_time_is_before :
      date_time_binary_op_has_type bop_date_time_is_before DateTime DateTime Bool 
  | tbop_date_time_is_after :
      date_time_binary_op_has_type bop_date_time_is_after DateTime DateTime Bool 
  | tbop_date_time_diff  :
      date_time_binary_op_has_type bop_date_time_diff DateTime DateTime DateTimeDuration
.

Definition math_binary_op_type_infer {model : brand_model} (op:math_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_math_atan2 =>
    if isFloat τ₁ && isFloat τ₂ then Some Float else None
  end.

Definition date_time_binary_op_type_infer {model : brand_model} (op:date_time_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_date_time_format =>
    if isDateTime τ₁ && isDateTimeFormat τ₂ then Some RType.String else None
  | bop_date_time_add =>
    if isDateTime τ₁ && isDateTimeDuration τ₂ then Some DateTime else None
  | bop_date_time_subtract =>
    if isDateTime τ₁ && isDateTimeDuration τ₂ then Some DateTime else None
  | bop_date_time_add_period =>
    if isDateTime τ₁ && isDateTimePeriod τ₂ then Some DateTime else None
  | bop_date_time_subtract_period =>
    if isDateTime τ₁ && isDateTimePeriod τ₂ then Some DateTime else None
  | bop_date_time_is_same =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_is_before =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_is_after =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_diff  =>
    if isDateTime τ₁ && isDateTime τ₂ then Some DateTimeDuration else None
  end.

Lemma math_binary_op_typing_sound {model : brand_model}
      (fb : math_binary_op) (τin₁ τin₂ τout : rtype) :
  math_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      math_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    inversion 1; subst;
      inversion 1; subst;
        invcs H0;
        invcs H1;
        simpl; 
        eexists; split; try reflexivity;
          repeat constructor.
Qed.

Lemma date_time_binary_op_typing_sound {model : brand_model}
      (fb : date_time_binary_op) (τin₁ τin₂ τout : rtype) :
  date_time_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      date_time_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    inversion 1; subst;
      inversion 1; subst;
        try invcs H0;
        try invcs H1;
        invcs H3;
        try invcs H4;
        simpl; 
        eexists; split; try reflexivity;
          repeat constructor.
Qed.

Definition math_binary_op_type_infer_sub {model : brand_model} (op:math_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_math_atan2 =>
    enforce_binary_op_schema (τ₁,Float) (τ₂,Float) Float
  end.

Definition date_time_binary_op_type_infer_sub {model : brand_model} (op:date_time_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_date_time_format =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimeFormat) RType.String
  | bop_date_time_add =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimeDuration) DateTime
  | bop_date_time_subtract =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimeDuration) DateTime
  | bop_date_time_add_period =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimePeriod) DateTime
  | bop_date_time_subtract_period =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimePeriod) DateTime
  | bop_date_time_is_same =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Bool
  | bop_date_time_is_before =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Bool
  | bop_date_time_is_after =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Bool
  | bop_date_time_diff  =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) DateTimeDuration
  end.

Inductive enhanced_binary_op_has_type {model:brand_model} :
  enhanced_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tenhanced_binary_math_op fb τin₁ τin₂ τout:
      math_binary_op_has_type fb τin₁ τin₂ τout ->
      enhanced_binary_op_has_type (enhanced_binary_math_op fb) τin₁ τin₂ τout
  | tenhanced_binary_date_time_op fb τin₁ τin₂ τout:
      date_time_binary_op_has_type fb τin₁ τin₂ τout ->
      enhanced_binary_op_has_type (enhanced_binary_date_time_op fb) τin₁ τin₂ τout.

Definition enhanced_binary_op_typing_infer {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_math_op fb => math_binary_op_type_infer fb τ₁ τ₂
  | enhanced_binary_date_time_op fb => date_time_binary_op_type_infer fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_infer_correct
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} :
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  intros.
  destruct fb; simpl.
  - destruct m; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
      ; destruct x; simpl in H; try discriminate
      ; destruct x0; simpl in H; try discriminate
      ; try (destruct ft; simpl in H; try discriminate)
      ; invcs H
      ; constructor
      ; repeat rewrite Float_canon
      ; repeat rewrite String_canon
      ; try constructor.
  - destruct d; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate;
        unfold isDateTime, isDateTimeDuration, isNat, isDateTimeFormat in *
        ; destruct x; simpl in H; try discriminate
        ; destruct ft; simpl in H; try discriminate
        ; destruct x0; simpl in H; try discriminate
        ; try (destruct ft; simpl in H; try discriminate)
        ; invcs H
        ; constructor
        ; repeat rewrite Nat_canon
        ; repeat rewrite Foreign_canon
        ; repeat rewrite String_canon
        ; try constructor.
Qed.

Lemma enhanced_binary_op_typing_infer_least
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout₁ τout₂} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fb; simpl.
  - destruct m; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
      ; destruct x; simpl in H; try discriminate
      ; destruct x0; simpl in H; try discriminate
      ; try (destruct ft; simpl in H; try discriminate)
      ; invcs H
      ; repeat rewrite Float_canon in H0
      ; invcs H0
      ; invcs H1
      ; reflexivity.
  - destruct d; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
      ; unfold isDateTime, isDateTimeDuration, isNat in *
      ; destruct x; simpl in H; try discriminate
      ; destruct ft; simpl in H; try discriminate
      ; destruct x0; simpl in H; try discriminate
      ; try (destruct ft; simpl in H; try discriminate)
      ; invcs H
      ; repeat rewrite Foreign_canon in H0
      ; invcs H0
      ; invcs H1
      ; reflexivity.
Qed.

Lemma enhanced_binary_op_typing_infer_complete
      {model:brand_model}
      (fb:foreign_operators_binary)
      {τ₁ τ₂ τout} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = None ->
  ~ enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  destruct fb; simpl; intros.
  - intro HH; invcs HH.
    destruct m; simpl in *; invcs H1; simpl in H; try discriminate.
  - intro HH; invcs HH.
    destruct d; simpl in *; invcs H1; simpl in H; try discriminate.
Qed.

Definition enhanced_binary_op_typing_infer_sub {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_math_op fb => math_binary_op_type_infer_sub fb τ₁ τ₂
  | enhanced_binary_date_time_op fb => date_time_binary_op_type_infer_sub fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_sound {model : brand_model}
      (fu : foreign_operators_binary) (τin₁ τin₂ τout : rtype) :
  enhanced_binary_op_has_type fu τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      enhanced_binary_op_interp brand_relation_brands fu din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply math_binary_op_typing_sound; eauto.
  - eapply date_time_binary_op_typing_sound; eauto.
Qed.

Instance enhanced_foreign_operators_typing
         {model:brand_model} :
  @foreign_operators_typing
    enhanced_foreign_data
    enhanced_foreign_operators
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_operators_typing_unary_has_type := enhanced_unary_op_has_type
       ; foreign_operators_typing_unary_sound := enhanced_unary_op_typing_sound
       ; foreign_operators_typing_unary_infer := enhanced_unary_op_typing_infer
       ; foreign_operators_typing_unary_infer_correct := enhanced_unary_op_typing_infer_correct
       ; foreign_operators_typing_unary_infer_least := enhanced_unary_op_typing_infer_least
       ; foreign_operators_typing_unary_infer_complete := enhanced_unary_op_typing_infer_complete
       ; foreign_operators_typing_unary_infer_sub := enhanced_unary_op_typing_infer_sub
       ; foreign_operators_typing_binary_has_type := enhanced_binary_op_has_type
       ; foreign_operators_typing_binary_sound := enhanced_binary_op_typing_sound
       ; foreign_operators_typing_binary_infer := enhanced_binary_op_typing_infer
       ; foreign_operators_typing_binary_infer_correct := enhanced_binary_op_typing_infer_correct
       ; foreign_operators_typing_binary_infer_least := enhanced_binary_op_typing_infer_least
       ; foreign_operators_typing_binary_infer_complete := enhanced_binary_op_typing_infer_complete
       ; foreign_operators_typing_binary_infer_sub := enhanced_binary_op_typing_infer_sub
     }.

Instance enhanced_foreign_typing {model:brand_model}:
  @foreign_typing
    enhanced_foreign_runtime
    enhanced_foreign_type
    model
  := mk_foreign_typing
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_data_typing
       enhanced_foreign_operators_typing.

