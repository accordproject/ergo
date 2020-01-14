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

Axiom MONETARY_AMOUNT_format : Float.float -> String.string -> String.string.
Extract Inlined Constant MONETARY_AMOUNT_format => "(fun x1 f -> Util.char_list_of_string (MonetaryAmount.amount_to_string_format x1 (Util.string_of_char_list f)))".

Axiom MONETARY_CODE_format : String.string -> String.string -> String.string.
Extract Inlined Constant MONETARY_CODE_format => "(fun x1 f -> Util.char_list_of_string (MonetaryAmount.code_to_string_format (Util.string_of_char_list x1) (Util.string_of_char_list f)))".

Inductive monetary_amount_binary_op :=
  | bop_monetary_amount_format
  | bop_monetary_code_format
.

Definition monetary_amount_binary_op_tostring (f:monetary_amount_binary_op) : String.string
  := match f with
     | bop_monetary_amount_format => "monetaryAmountFormat"
     | bop_monetary_code_format => "monetaryCodeFormat"
     end.

(* Java equivalent: JavaScriptBackend.jsFunc *)
Definition jsFunc (name:string) (dl:list string)
  := name ++ "(" ++ (String.concat ", " dl) ++ ")".
Definition jsFuncBinary (name:string) (d1 d2:string)
  := jsFunc name (d1::d2::nil).

Definition mk_java_binary_opn (opname:string) (sn:list string) (el:list java_json) : java_json
  := mk_java_json
       ("BinaryOperators."
          ++ opname
          ++ "("
          ++ (String.concat ", " (List.app sn (List.map from_java_json el)))
          ++ ")").

Definition monetary_amount_to_java_binary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fb:monetary_amount_binary_op)
           (d1 d2:java_json) : java_json
  := match fb with
     | bop_monetary_amount_format => mk_java_binary_op0 "monetary_amount_format" d1 d2
     | bop_monetary_code_format => mk_java_binary_op0 "monetary_code_format" d1 d2
     end.

Definition monetary_amount_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:monetary_amount_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_monetary_amount_format => jsFuncBinary "monetaryAmountFormat" d1 d2
     | bop_monetary_code_format => jsFuncBinary "monetaryCodeFormat" d1 d2
     end.

Definition monetary_amount_to_ajavascript_binary_op
             (fb:monetary_amount_binary_op)
             (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | bop_monetary_amount_format => call_runtime "monetaryAmountFormat" (e1::e2::nil)
     | bop_monetary_code_format => call_runtime "monetaryCodeFormat" (e1::e2::nil)
     end.

