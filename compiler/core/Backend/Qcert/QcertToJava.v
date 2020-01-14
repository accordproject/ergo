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

Require Import Qcert.Utils.Utils.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.Java.JavaSystem.
Require Import Qcert.Translation.Operators.ForeignToJava.

Require Import QcertData.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Local Open Scope nstring_scope.

(* XXX TODO: fix me *)
Definition enhanced_to_java_data
           (quotel:nstring) (fd:enhanced_data) : java_json
  := match fd with
     | enhanceddateTimeformat f => mk_java_json (^@toString _ date_time_format_foreign_data.(@foreign_data_tostring ) f)
     | enhanceddateTime f => mk_java_json (^@toString _ date_time_foreign_data.(@foreign_data_tostring ) f)
     | enhanceddateTimeduration f => mk_java_json (^@toString _ date_time_duration_foreign_data.(@foreign_data_tostring ) f)
     | enhanceddateTimeperiod f => mk_java_json (^@toString _ date_time_period_foreign_data.(@foreign_data_tostring ) f)
     end.

Definition enhanced_to_java_unary_op
           (indent:nat) (eol:nstring)
           (quotel:nstring) (fu:enhanced_unary_op)
           (d:java_json) : java_json
  := match fu with
     | enhanced_unary_uri_op op =>
       uri_to_java_unary_op indent eol quotel op d
     | enhanced_unary_log_op op =>
       log_to_java_unary_op indent eol quotel op d
     | enhanced_unary_math_op op =>
       math_to_java_unary_op indent eol quotel op d
     | enhanced_unary_date_time_op op =>
       date_time_to_java_unary_op indent eol quotel op d
     end.

Definition enhanced_to_java_binary_op
           (indent:nat) (eol:nstring)
           (quotel:nstring) (fb:enhanced_binary_op)
           (d1 d2:java_json) : java_json
  := match fb with
     | enhanced_binary_math_op op =>
       math_to_java_binary_op indent eol quotel op d1 d2
     | enhanced_binary_date_time_op op =>
       date_time_to_java_binary_op indent eol quotel op d1 d2
     end.

Instance enhanced_foreign_to_java :
  @foreign_to_java enhanced_foreign_runtime
  := mk_foreign_to_java
       enhanced_foreign_runtime
       enhanced_to_java_data
       enhanced_to_java_unary_op
       enhanced_to_java_binary_op.

