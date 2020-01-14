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

Require Import QcertData.
Require Import QcertToSpark.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

(** Foreign typing, used to build the basic_model *)

Inductive enhanced_type : Set :=
  | enhancedTop : enhanced_type
  | enhancedBottom : enhanced_type
  | enhancedString : enhanced_type
  | enhancedDateTimeFormat : enhanced_type
  | enhancedDateTime : enhanced_type
  | enhancedDateTimeDuration : enhanced_type
  | enhancedDateTimePeriod : enhanced_type
.

Definition enhanced_type_to_string (et:enhanced_type) : string :=
  match et with
  | enhancedTop => "ETop"
  | enhancedBottom => "EBottom"
  | enhancedString => "EString"
  | enhancedDateTimeFormat => "EDateTimeFormat"
  | enhancedDateTime => "EDateTime"
  | enhancedDateTimeDuration => "EDateTimeDuration"
  | enhancedDateTimePeriod => "EDateTimePeriod"
  end.

Definition string_to_enhanced_type (s:string) : option enhanced_type :=
  match s with
  | "ETop"%string => Some enhancedTop
  | "EBottom"%string => Some enhancedBottom
  | "EString"%string => Some enhancedString
  | "EDateTimeFormat"%string => Some enhancedDateTimeFormat
  | "EDateTime"%string => Some enhancedDateTime
  | "EDateTimeDuration"%string => Some enhancedDateTimeDuration
  | "EDateTimePeriod"%string => Some enhancedDateTimePeriod
  | _ => None
  end.

Definition enhanced_type_join (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedBottom, _ => t2
     | _, enhancedBottom => t1
     | enhancedString, enhancedString => enhancedString
     | enhancedDateTimeFormat, enhancedDateTimeFormat => enhancedDateTimeFormat
     | enhancedDateTime, enhancedDateTime => enhancedDateTime
     | enhancedDateTimeDuration, enhancedDateTimeDuration => enhancedDateTimeDuration
     | enhancedDateTimePeriod, enhancedDateTimePeriod => enhancedDateTimePeriod
     | _, _ => enhancedTop
     end.

Definition enhanced_type_meet (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedTop, _ => t2
     | _, enhancedTop => t1
     | enhancedString, enhancedString => enhancedString
     | enhancedDateTimeFormat, enhancedDateTimeFormat => enhancedDateTimeFormat
     | enhancedDateTime, enhancedDateTime => enhancedDateTime
     | enhancedDateTimeDuration, enhancedDateTimeDuration => enhancedDateTimeDuration
     | enhancedDateTimePeriod, enhancedDateTimePeriod => enhancedDateTimePeriod
     | _, _ => enhancedBottom
     end.

Inductive enhanced_subtype : enhanced_type -> enhanced_type -> Prop :=
| enhanced_subtype_top t : enhanced_subtype t enhancedTop
| enhanced_subtype_bottom t : enhanced_subtype enhancedBottom t
| enhanced_subtype_refl t : enhanced_subtype t t.

Instance enhanced_subtype_pre : PreOrder enhanced_subtype.
Proof.
  constructor; red; intros.
  - destruct x; constructor.
  - inversion H; inversion H0; subst; try constructor; congruence.
Qed.

Instance enhanced_subtype_post : PartialOrder eq enhanced_subtype.
Proof.
  intros x y; split.
  - intros; subst.
    repeat red.
    split; constructor.
  - destruct 1.
    inversion H; inversion H0; congruence.
Qed.

Instance enhanced_type_lattice : Lattice enhanced_type eq
  := {
      join := enhanced_type_join
      ; meet := enhanced_type_meet
    }.
Proof.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
      reflexivity.
  - red; intros t1.
    simpl.
    destruct t1; simpl; try reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
      reflexivity.
  - red; intros t1.
    destruct t1; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
Defined.

Instance enhanced_type_olattice : OLattice eq enhanced_subtype.
Proof.
  constructor.
  split.
  - destruct a; destruct b; inversion 1; simpl; reflexivity.
  - destruct a; destruct b; inversion 1; simpl;
      constructor.
Qed.

Program Instance enhanced_foreign_type : foreign_type
  := mk_foreign_type enhanced_type _ _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  intros.
  change ({x = y} + {x <> y}).
  decide equality.
Defined.
Next Obligation.
  destruct a; destruct b; try solve [left; constructor | right; inversion 1].
Defined.

