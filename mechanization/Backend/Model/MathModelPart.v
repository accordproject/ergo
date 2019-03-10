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

(** Additional math built-in functions *)

(** Constants *)

Axiom FLOAT_PI : float.
Axiom FLOAT_E : float.

(** Unary operators *)

(* Axioms *)
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

(* Ast *)
Inductive math_unary_op
  :=
  | uop_math_of_string : math_unary_op
  | uop_math_acos : math_unary_op
  | uop_math_asin : math_unary_op
  | uop_math_atan : math_unary_op
  | uop_math_cos : math_unary_op
  | uop_math_cosh : math_unary_op
  | uop_math_sin : math_unary_op
  | uop_math_sinh : math_unary_op
  | uop_math_tan : math_unary_op
  | uop_math_tanh : math_unary_op
.

Definition math_unary_op_tostring (f:math_unary_op) : String.string
  := match f with
     | uop_math_of_string => "floatOfString"
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

(* Code generation *)
Definition math_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:math_unary_op)
             (d:java_json) : java_json
  := match fu with
     | uop_math_of_string => mk_java_unary_op0 "floatOfString" d
     | uop_math_acos => mk_java_unary_op0 "acos" d
     | uop_math_asin => mk_java_unary_op0 "asin" d
     | uop_math_atan => mk_java_unary_op0 "atan" d
     | uop_math_cos => mk_java_unary_op0 "cos" d
     | uop_math_cosh => mk_java_unary_op0 "cosh" d
     | uop_math_sin => mk_java_unary_op0 "sin" d
     | uop_math_sinh => mk_java_unary_op0 "sinh" d
     | uop_math_tan => mk_java_unary_op0 "tan" d
     | uop_math_tanh => mk_java_unary_op0 "tanh" d
     end.

Definition math_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:math_unary_op)
             (d:String.string) : String.string
  := match fu with
     | uop_math_of_string => "floatOfString(" ++ d ++ ")"
     | uop_math_acos => "acos(" ++ d ++ ")"
     | uop_math_asin => "asin(" ++ d ++ ")"
     | uop_math_atan => "atan(" ++ d ++ ")"
     | uop_math_cos => "cos(" ++ d ++ ")"
     | uop_math_cosh => "cosh(" ++ d ++ ")"
     | uop_math_sin => "sin(" ++ d ++ ")"
     | uop_math_sinh => "sinh(" ++ d ++ ")"
     | uop_math_tan => "tan(" ++ d ++ ")"
     | uop_math_tanh => "tanh(" ++ d ++ ")"
     end.

Definition math_to_ajavascript_unary_op
             (fu:math_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | uop_math_of_string => call_runtime "floatOfString" [ e ]
     | uop_math_acos => call_runtime "acos" [ e ]
     | uop_math_asin => call_runtime "asin" [ e ]
     | uop_math_atan => call_runtime "atan" [ e ]
     | uop_math_cos => call_runtime "cos" [ e ]
     | uop_math_cosh => call_runtime "cosh" [ e ]
     | uop_math_sin => call_runtime "sin" [ e ]
     | uop_math_sinh => call_runtime "sinh" [ e ]
     | uop_math_tan => call_runtime "tan" [ e ]
     | uop_math_tanh => call_runtime "tanh" [ e ]
     end.

(** Binary operators *)

(* Axioms *)
Axiom FLOAT_atan2 : float -> float -> float.
Extract Inlined Constant FLOAT_atan2 => "(fun x y -> atan2 x y)".

(* Ast *)
Inductive math_binary_op
  :=
  | bop_math_atan2 : math_binary_op
.

Definition math_binary_op_tostring (f:math_binary_op) : String.string
  := match f with
     | bop_math_atan2 => "atan2"
     end.

(* Code generation *)
Definition math_to_java_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:math_binary_op)
             (d1 d2:java_json) : java_json
  := match fb with
     | bop_math_atan2 => mk_java_binary_op0 "atan2" d1 d2
     end.

Definition math_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:math_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_math_atan2 => jsFunc "atan2" d1 d2
     end.  

Definition math_to_ajavascript_binary_op
             (fb:math_binary_op)
             (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | bop_math_atan2 => call_runtime "atan2" [ e1; e2 ]
     end.  

