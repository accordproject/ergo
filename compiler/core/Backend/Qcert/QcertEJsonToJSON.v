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
Require Import Qcert.EJson.EJsonSystem.
Require Import Qcert.JSON.JSONSystem.
Require Import Qcert.Translation.Model.ForeignDataToEJson.
Require Import Qcert.Translation.Model.ForeignEJsonToJSON.
Require Import Qcert.Translation.Operators.ForeignToEJsonRuntime.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Require Import QcertData.
Require Import QcertEJson.

Import ListNotations.
Local Open Scope list_scope.

Definition enhanced_foreign_json_to_ejson (j:json) : option enhanced_ejson :=
  match j with
  | jobject (("$format"%string,jstring s)::nil) =>
    Some (enhanceddateTimeformat (DATE_TIME_FORMAT_from_string s))
  | jobject (("$date"%string,jstring s)::nil) =>
    Some (enhanceddateTime (DATE_TIME_from_string s))
  | jobject (("$duration"%string,jstring s)::nil) =>
    Some (enhanceddateTimeduration (DATE_TIME_DURATION_from_string s))
  | jobject (("$period"%string,jstring s)::nil) =>
    Some (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_string s))
  | _ => None
  end.

Definition enhanced_foreign_ejson_to_json (ej:enhanced_ejson) : json :=
  match ej with
  | enhanceddateTimeformat f =>
    jobject (("$format"%string,jstring (DATE_TIME_FORMAT_to_string f))::nil)
  | enhanceddateTime f =>
    jobject (("$date"%string,jstring (DATE_TIME_to_string f))::nil)
  | enhanceddateTimeduration f =>
    jobject (("$duration"%string,jstring (DATE_TIME_DURATION_to_string f))::nil)
  | enhanceddateTimeperiod f =>
    jobject (("$period"%string,jstring (DATE_TIME_PERIOD_to_string f))::nil)
  end.

Program Instance enhanced_foreign_to_json : foreign_to_json
  := mk_foreign_to_json enhanced_foreign_ejson _ _.
Next Obligation.
  exact (enhanced_foreign_json_to_ejson fd).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_to_json j).
Defined.

