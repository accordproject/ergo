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
Require Import Qcert.Java.JavaRuntime.

Import ListNotations.
Local Open Scope string.
Local Open Scope nstring_scope.

Axiom MONETARY_AMOUNT_format : FloatAdd.float -> String.string -> String.string.
Extract Inlined Constant MONETARY_AMOUNT_format => "(fun x1 f -> Util.char_list_of_string (MonetaryAmount.amount_to_string_format x1 (Util.string_of_char_list f)))".

Axiom MONETARY_CODE_format : String.string -> String.string -> String.string.
Extract Inlined Constant MONETARY_CODE_format => "(fun x1 f -> Util.char_list_of_string (MonetaryAmount.code_to_string_format (Util.string_of_char_list x1) (Util.string_of_char_list f)))".

Section MonetaryAmountOperators.
  (** Binary operators *)
  Inductive monetary_amount_binary_op :=
  | bop_monetary_amount_format
  | bop_monetary_code_format
  .

  Section toString.
    Definition monetary_amount_binary_op_tostring (f:monetary_amount_binary_op) : String.string
      := match f with
         | bop_monetary_amount_format => "monetaryAmountFormat"
         | bop_monetary_code_format => "monetaryCodeFormat"
         end.
  End toString.

  Section toJava.
    Definition cname : nstring := ^"MonetaryAmountComponent".

    Definition monetary_amount_to_java_binary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fb:monetary_amount_binary_op)
               (d1 d2:java_json) : java_json
      := match fb with
         | bop_monetary_amount_format => mk_java_binary_op0_foreign cname (^"monetary_amount_format") d1 d2
         | bop_monetary_code_format => mk_java_binary_op0_foreign cname (^"monetary_code_format") d1 d2
         end.

  End toJava.

  Section toEJson.
    Inductive ejson_monetary_amount_runtime_op :=
    (* Binary *)
    | EJsonRuntimeMonetaryAmountFormat
    | EJsonRuntimeMonetaryCodeFormat
    .

    Definition ejson_monetary_amount_runtime_op_tostring op : string :=
      match op with
      | EJsonRuntimeMonetaryAmountFormat => "monetaryAmountFormat"
      | EJsonRuntimeMonetaryCodeFormat => "monetaryCodeFormat"
      end.

    Definition ejson_monetary_amount_runtime_op_fromstring (s:string) : option ejson_monetary_amount_runtime_op :=
      match s with
      | "monetaryAmountFormat" => Some EJsonRuntimeMonetaryAmountFormat
      | "monetaryCodeFormat" => Some EJsonRuntimeMonetaryCodeFormat
      | _ => None
      end.

  End toEJson.
  
End MonetaryAmountOperators.
