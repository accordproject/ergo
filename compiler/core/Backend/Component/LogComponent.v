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
Require Import Qcert.Data.Model.ForeignData.
Require Import Qcert.Data.Operators.ForeignOperators.
Require Import Qcert.Translation.Operators.ForeignToJava.
Require Import Qcert.Java.JavaSystem.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

(** Log functions part of the Ergo Standard Library *)

(** Axioms *)
Axiom LOG_string : string -> unit.
Extract Inlined Constant LOG_string => "(fun x -> Logger.log_string x)".
Axiom LOG_encode_string : string -> string.

Section LogOperators.
  (** Ast *)
  Inductive log_unary_op :=
  | uop_log_string : log_unary_op
  .

  Section toString.
    Definition log_unary_op_tostring (f:log_unary_op) : string :=
      match f with
      | uop_log_string => "logString"
      end.

  End toString.

  Section toJava.
    Definition cname : nstring := ^"LogComponent".

    Definition log_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:log_unary_op)
               (d:java_json) : java_json
      := match fu with
         | uop_log_string => mk_java_unary_op0_foreign cname (^"logString") d
         end.

  End toJava.

  Section toEJson.
    Inductive ejson_log_runtime_op :=
    | EJsonRuntimeLogString
    .

    Definition ejson_log_runtime_op_tostring op : string :=
      match op with
      | EJsonRuntimeLogString => "logString"
      end.

  End toEJson.
End LogOperators.
