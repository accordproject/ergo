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
Require Import Qcert.Translation.Operators.ForeignToReduceOps.

Require Import QcertData.
Require Import QcertReduceOps.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

Definition enhanced_to_reduce_op (uop:unary_op) : option NNRCMR.reduce_op :=
  match uop with
  | OpCount => Some (NNRCMR.RedOpForeign RedOpCount)
  | OpNatSum =>
    Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int))
  | OpFloatSum =>
    Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float))
  | OpNatMin =>
    Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int))
  | OpFloatBagMin =>
    Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float))
  | OpNatMax =>
    Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int))
  | OpFloatBagMax =>
    Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float))
  | OpNatMean =>
    Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int))
  | OpFloatMean =>
    Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float))
  | _ => None
  end.

Definition enhanced_of_reduce_op (rop:NNRCMR.reduce_op) : option unary_op :=
  match rop with
  | NNRCMR.RedOpForeign RedOpCount => Some OpCount
  | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int) =>
    Some (OpNatSum)
  | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float) =>
    Some (OpFloatSum)
  | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int) =>
    Some (OpNatMin)
  | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float) =>
    Some (OpFloatBagMin)
  | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int) =>
    Some (OpNatMax)
  | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float) =>
    Some (OpFloatBagMax)
  | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int) =>
    Some (OpNatMean)
  | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float) =>
    Some (OpFloatMean)
  | NNRCMR.RedOpForeign (RedOpStats _) =>
    None (* XXX TODO? XXX *)
  end.

Program Instance enhanced_foreign_to_reduce_op : foreign_to_reduce_op :=
  mk_foreign_to_reduce_op enhanced_foreign_runtime enhanced_foreign_reduce_op enhanced_to_reduce_op _ enhanced_of_reduce_op _.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct uop; simpl in *; invcs H; try reflexivity.
Qed.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct rop; simpl in *; invcs H; try reflexivity.
  destruct f; invcs H1; simpl; try reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
Qed.
