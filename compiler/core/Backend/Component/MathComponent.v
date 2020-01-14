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

(** Math functions (trigonometric, etc) part of the Ergo Standard Library *)

(** Axioms *)

(** Constants *)
Axiom FLOAT_PI : float.
Axiom FLOAT_E : float.

(** Unary operators *)
Axiom FLOAT_of_string : string -> option float.
Extract Inlined Constant FLOAT_of_string => "(fun x -> Util.ergo_float_of_string x)".

Axiom FLOAT_acos : float -> float.
Extract Inlined Constant FLOAT_acos => "(fun x -> acos x)".
Axiom FLOAT_asin : float -> float.
Extract Inlined Constant FLOAT_asin => "(fun x -> asin x)".
Axiom FLOAT_atan : float -> float.
Extract Inlined Constant FLOAT_atan => "(fun x -> atan x)".

Axiom FLOAT_cos : float -> float.
Extract Inlined Constant FLOAT_cos => "(fun x -> cos x)".
Axiom FLOAT_cosh : float -> float.
Extract Inlined Constant FLOAT_cosh => "(fun x -> cosh x)".

Axiom FLOAT_sin : float -> float.
Extract Inlined Constant FLOAT_sin => "(fun x -> sin x)".
Axiom FLOAT_sinh : float -> float.
Extract Inlined Constant FLOAT_sinh => "(fun x -> sinh x)".

Axiom FLOAT_tan : float -> float.
Extract Inlined Constant FLOAT_tan => "(fun x -> tan x)".
Axiom FLOAT_tanh : float -> float.
Extract Inlined Constant FLOAT_tanh => "(fun x -> tanh x)".

(** Binary operators *)
Axiom FLOAT_atan2 : float -> float -> float.
Extract Inlined Constant FLOAT_atan2 => "(fun x y -> atan2 x y)".

Section MathOperators.
  (** Ast *)
  Inductive math_unary_op :=
  | uop_math_float_of_string
  | uop_math_acos
  | uop_math_asin
  | uop_math_atan
  | uop_math_cos
  | uop_math_cosh
  | uop_math_sin
  | uop_math_sinh
  | uop_math_tan
  | uop_math_tanh
  .

  Inductive math_binary_op :=
  | bop_math_atan2
  .

  Section toString.
    Definition math_unary_op_tostring (f:math_unary_op) : string :=
      match f with
      | uop_math_float_of_string => "floatOfString"
      | uop_math_acos => "acos"
      | uop_math_asin => "asin"
      | uop_math_atan => "atan"
      | uop_math_cos => "cos"
      | uop_math_cosh => "cosh"
      | uop_math_sin => "sin"
      | uop_math_sinh => "sinh"
      | uop_math_tan => "tan"
      | uop_math_tanh => "tanh"
      end.

    Definition math_binary_op_tostring (f:math_binary_op) : string :=
      match f with
      | bop_math_atan2 => "atan2"
      end.

  End toString.

  Section toJava.
    Definition cname : nstring := ^"MathComponent".

    Definition math_to_java_unary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fu:math_unary_op)
               (d:java_json) : java_json :=
      match fu with
      | uop_math_float_of_string => mk_java_unary_op0_foreign cname (^"floatOfString") d
      | uop_math_acos => mk_java_unary_op0_foreign cname (^"acos") d
      | uop_math_asin => mk_java_unary_op0_foreign cname (^"asin") d
      | uop_math_atan => mk_java_unary_op0_foreign cname (^"atan") d
      | uop_math_cos => mk_java_unary_op0_foreign cname (^"cos") d
      | uop_math_cosh => mk_java_unary_op0_foreign cname (^"cosh") d
      | uop_math_sin => mk_java_unary_op0_foreign cname (^"sin") d
      | uop_math_sinh => mk_java_unary_op0_foreign cname (^"sinh") d
      | uop_math_tan => mk_java_unary_op0_foreign cname (^"tan") d
      | uop_math_tanh => mk_java_unary_op0_foreign cname (^"tanh") d
      end.

    Definition math_to_java_binary_op
               (indent:nat) (eol:nstring)
               (quotel:nstring) (fb:math_binary_op)
               (d1 d2:java_json) : java_json :=
      match fb with
      | bop_math_atan2 => mk_java_binary_op0_foreign cname (^"atan2") d1 d2
      end.

  End toJava.

  Section toEJson.
    Inductive ejson_math_runtime_op :=
    | EJsonRuntimeFloatOfString
    | EJsonRuntimeAcos
    | EJsonRuntimeAsin
    | EJsonRuntimeAtan
    | EJsonRuntimeAtan2
    | EJsonRuntimeCos
    | EJsonRuntimeCosh
    | EJsonRuntimeSin
    | EJsonRuntimeSinh
    | EJsonRuntimeTan
    | EJsonRuntimeTanh
    .

    Definition ejson_math_runtime_op_tostring op : string :=
      match op with
      | EJsonRuntimeFloatOfString => "floatOfString"
      | EJsonRuntimeAcos => "acos"
      | EJsonRuntimeAsin => "asin"
      | EJsonRuntimeAtan => "atan"
      | EJsonRuntimeAtan2 => "atan2"
      | EJsonRuntimeCos => "cos"
      | EJsonRuntimeCosh => "cosh"
      | EJsonRuntimeSin => "sin"
      | EJsonRuntimeSinh => "sinh"
      | EJsonRuntimeTan => "tan"
      | EJsonRuntimeTanh => "tanh"
      end.

  End toEJson.
End MathOperators.
