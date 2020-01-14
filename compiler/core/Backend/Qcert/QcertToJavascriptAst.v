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

Require Import Qcert.EJson.EJsonSystem.
Require Import Qcert.Translation.Operators.ForeignToJavaScriptAst.

Require Import QcertData.
Require Import QcertEJson.

(* XXX TODO This is very wrong *)
Definition enhanced_ejson_to_ajavascript_expr (j:enhanced_ejson) : JsAst.JsSyntax.expr :=
  JsAst.JsSyntax.expr_literal (JsAst.JsSyntax.literal_null).

Instance enhanced_foreign_ejson_to_ajavascript :
  @foreign_ejson_to_ajavascript enhanced_foreign_ejson
  := mk_foreign_ejson_to_ajavascript
       enhanced_foreign_ejson
       enhanced_ejson_to_ajavascript_expr.

