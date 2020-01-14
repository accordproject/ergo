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
Require Import Qcert.NNRCMR.Lang.ForeignReduceOps.

Require Import QcertData.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

Inductive enhanced_numeric_type :=
| enhanced_numeric_int
| enhanced_numeric_float.

Global Instance enhanced_numeric_type_eqdec : EqDec enhanced_numeric_type eq.
Proof.
  red. unfold equiv, complement.
  change (forall x y : enhanced_numeric_type, {x = y} + {x <> y}).
  decide equality.
Defined.

Inductive enhanced_reduce_op
  := RedOpCount : enhanced_reduce_op
   | RedOpSum (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMin (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMax (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpArithMean (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpStats (typ:enhanced_numeric_type) : enhanced_reduce_op.

Definition enhanced_numeric_type_prefix
           (typ:enhanced_numeric_type) : string
  := match typ with
     | enhanced_numeric_int => ""%string
     | enhanced_numeric_float => "F"%string
     end.

Definition enhanced_reduce_op_tostring (op:enhanced_reduce_op) : string
  := match op with
     | RedOpCount => "COUNT"%string
     | RedOpSum typ => append (enhanced_numeric_type_prefix typ) "FSUM"%string
     | RedOpMin typ  => append (enhanced_numeric_type_prefix typ) "FMIN"%string
     | RedOpMax typ => append (enhanced_numeric_type_prefix typ) "FMAX"%string
     | RedOpArithMean typ => append (enhanced_numeric_type_prefix typ) "FARITHMEAN"%string
     | RedOpStats typ => append (enhanced_numeric_type_prefix typ) "FSTATS"%string
     end.

Definition enhanced_numeric_sum (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatSum
     | enhanced_numeric_float
       => OpFloatSum
     end.

Definition enhanced_numeric_min (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMin
     | enhanced_numeric_float
       => OpFloatBagMin
     end.

Definition enhanced_numeric_max (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMax
     | enhanced_numeric_float
       => OpFloatBagMax
     end.

Definition enhanced_numeric_arith_mean (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMean
     | enhanced_numeric_float
       => OpFloatMean
     end.

Definition enhanced_reduce_op_interp
           (br:brand_relation_t)
           (op:enhanced_reduce_op)
           (dl:list data) : option data
  := match op with
     | RedOpCount | RedOpSum _ | RedOpMin _ | RedOpMax _ | RedOpArithMean _ =>
                                                           let uop :=
                                                               match op with
                                                               | RedOpCount  => OpCount
                                                               | RedOpSum typ => enhanced_numeric_sum typ
                                                               | RedOpMin typ => enhanced_numeric_min typ
                                                               | RedOpMax typ => enhanced_numeric_max typ
                                                               | RedOpArithMean typ => enhanced_numeric_arith_mean typ
                                                               | RedOpStats _ => OpCount (* assert false *)
                                                               end
                                                           in
                                                           unary_op_eval br uop (dcoll dl) 
     | RedOpStats typ =>
       let coll := dcoll dl in
       let count := unary_op_eval br OpCount coll in
       let sum := unary_op_eval br (enhanced_numeric_sum typ) coll in
       let min := unary_op_eval br (enhanced_numeric_min typ) coll in
       let max := unary_op_eval br (enhanced_numeric_max typ) coll in
       let v :=
           match (count, sum, min, max) with
           | (Some count, Some sum, Some min, Some max) =>
             Some (drec (("count"%string, count)
                           ::("max"%string, max)
                           ::("min"%string, min)
                           ::("sum"%string, sum)
                           ::nil))
           | _ => None
           end
       in
       v
     end.

Program Instance enhanced_foreign_reduce_op : foreign_reduce_op
  := mk_foreign_reduce_op enhanced_foreign_data enhanced_reduce_op _ _ enhanced_reduce_op_interp _.
Next Obligation.
  red; unfold equiv, complement.
  change (forall x y:enhanced_reduce_op, {x = y} + {x <> y}).
  decide equality; decide equality.
Defined.
Next Obligation.
  constructor.
  apply enhanced_reduce_op_tostring.
Defined.
Next Obligation.
  destruct op; simpl in *; invcs H.
  - constructor.
  - destruct typ; simpl in *.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_min in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmin in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + destruct (dsum dl); simpl in *; try discriminate.
      unfold lifted_min, lifted_max in *.
      destruct ((lift bnummin (lifted_zbag dl))); simpl in *; try discriminate.
      destruct ((lift bnummax (lifted_zbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
      * reflexivity.
    + case_eq (lifted_fsum dl); intros; simpl in *; rewrite H in *; try discriminate.
      unfold lifted_fmin, lifted_fmax in *.
      destruct ((lift float_list_min (lifted_fbag dl))); simpl in *; try discriminate.
      destruct ((lift float_list_max (lifted_fbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
        apply some_lift in H; destruct H as [? eqq ?]; subst.
        constructor.
      * reflexivity.
Qed.

