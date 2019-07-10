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
Require Import Qcert.Common.DataModel.ForeignData.
Require Import Qcert.Common.Operators.ForeignOperators.
Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Translation.ForeignToJava.
Require Import Qcert.Translation.NNRCtoJava.

Import ListNotations.
Local Open Scope string.

(* Java equivalent: JavaScriptBackend.jsFunc *)
Definition jsFunc (name d1 d2:string)
  := name ++ "(" ++ d1 ++ ", " ++ d2 ++ ")".

(** Additional logging functions *)

(** Unary operators *)

(* Axioms *)
Axiom LOG_string : string -> unit.
Extract Inlined Constant LOG_string => "(fun x -> Logger.log_string x)".
Axiom LOG_encode_string : string -> string.
Extract Inlined Constant LOG_encode_string => "(fun x -> Util.encode_string x)".
Axiom LOG_decode_string : string -> string.
Extract Inlined Constant LOG_decode_string => "(fun x -> Util.decode_string x)".

(* Ast *)
Inductive log_unary_op
  :=
  | uop_log_string : log_unary_op
  | uop_log_encode_string : log_unary_op
  | uop_log_decode_string : log_unary_op
.

Definition log_unary_op_tostring (f:log_unary_op) : String.string
  := match f with
     | uop_log_string => "logString"
     | uop_log_encode_string => "encodeString"
     | uop_log_decode_string => "decodeString"
     end.

(* Code generation *)
Definition log_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:log_unary_op)
             (d:java_json) : java_json
  := match fu with
     | uop_log_string => mk_java_unary_op0 "logString" d
     | uop_log_encode_string => mk_java_unary_op0 "encodeString" d
     | uop_log_decode_string => mk_java_unary_op0 "decodeString" d
     end.

Definition log_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:log_unary_op)
             (d:String.string) : String.string
  := match fu with
     | uop_log_string => "logString(" ++ d ++ ")"
     | uop_log_encode_string => "encodeString(" ++ d ++ ")"
     | uop_log_decode_string => "decodeString(" ++ d ++ ")"
     end.

Definition log_to_ajavascript_unary_op
             (fu:log_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | uop_log_string => call_runtime "logString" [ e ]
     | uop_log_encode_string => call_runtime "encodeString" [ e ]
     | uop_log_decode_string => call_runtime "decodeString" [ e ]
     end.

