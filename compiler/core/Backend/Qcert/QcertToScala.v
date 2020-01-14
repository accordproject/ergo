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
Require Import Qcert.TypeSystem.ForeignType.
Require Import Qcert.Translation.Model.ForeignTypeToJSON.
Require Import Qcert.Translation.Operators.ForeignToScala.

Require Import QcertData.
Require Import QcertEJson.
Require Import QcertDataToEJson.
Require Import QcertEJsonToJSON.
Require Import QcertToJava.
Require Import QcertType.

Local Open Scope nstring_scope.

Definition enhanced_to_scala_unary_op (op: enhanced_unary_op) (d: nstring) : nstring :=
  match op with
  | enhanced_unary_uri_op op => ^"QcertModel: uri ops not supported for now."
  | enhanced_unary_log_op op => ^"QcertModel: log ops not supported for now."
  | enhanced_unary_math_op op => ^"QcertModel: math ops not supported for now."
  | enhanced_unary_date_time_op op => ^"QcertModel: date time ops not supported for now."
  end.

Definition enhanced_to_scala_spark_datatype (ft: foreign_type_type) : nstring :=
  (* XXX This is obviously not correct. Where is the place to put this? *)
  ^"FloatType".

Instance enhanced_foreign_to_scala:
  @foreign_to_scala enhanced_foreign_runtime _
  := mk_foreign_to_scala
       enhanced_foreign_runtime _
       enhanced_to_scala_unary_op
       enhanced_to_scala_spark_datatype.

