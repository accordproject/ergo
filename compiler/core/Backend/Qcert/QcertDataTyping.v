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
Require Import Qcert.JSON.JSONSystem.
Require Import Qcert.Data.DataSystem.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Require Import QcertData.
Require Import QcertType.

Inductive enhanced_has_type : enhanced_data -> enhanced_type -> Prop :=
| enhanced_has_type_top fd : enhanced_has_type fd enhancedTop
| enhanced_has_type_dateTimeFormat (tp:DATE_TIME_FORMAT) : enhanced_has_type (enhanceddateTimeformat tp) enhancedDateTimeFormat
| enhanced_has_type_dateTime (tp:DATE_TIME) : enhanced_has_type (enhanceddateTime tp) enhancedDateTime
| enhanced_has_type_dateTimeduration (tp:DATE_TIME_DURATION) : enhanced_has_type (enhanceddateTimeduration tp) enhancedDateTimeDuration
| enhanced_has_type_dateTimeperiod (tp:DATE_TIME_PERIOD) : enhanced_has_type (enhanceddateTimeperiod tp) enhancedDateTimePeriod
.

Definition enhanced_infer_type (d:enhanced_data) : option enhanced_type
  := match d with
     | enhanceddateTimeformat _ => Some enhancedDateTimeFormat
     | enhanceddateTime _ => Some enhancedDateTime
     | enhanceddateTimeduration _ => Some enhancedDateTimeDuration
     | enhanceddateTimeperiod _ => Some enhancedDateTimePeriod
     end.

Program Instance enhanced_foreign_data_typing :
  @foreign_data_typing enhanced_foreign_data enhanced_foreign_type
  := mk_foreign_data_typing
       enhanced_foreign_data
       enhanced_foreign_type
       enhanced_has_type _ _ _
       enhanced_infer_type _ _ _
.
Next Obligation.
  inversion H; subst;
    simpl; trivial.
  - destruct d; simpl; constructor.
  - constructor.
  - constructor.
  - constructor.
Defined.
Next Obligation.
  inversion H0; subst; simpl.
  - constructor.
  - inversion H.
  - trivial.
Defined.
Next Obligation.
  inversion H; inversion H0; subst; simpl; try constructor; congruence.
Defined.
Next Obligation.
  destruct d; simpl; eexists; reflexivity.
Defined.
Next Obligation.
  destruct d; simpl in H; invcs H; constructor.
Defined.
Next Obligation.
  destruct d; simpl in H, H0
  ; invcs H; invcs H0; constructor.
Defined.

