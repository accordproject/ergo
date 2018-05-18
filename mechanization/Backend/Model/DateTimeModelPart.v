(*
 * Copyright 2015-2016 IBM Corporation
 *
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

Import ListNotations.

(*********  <WARNING>*********************)
(** Extraction to OCaml is currently a stub **)
(********* </WARNING> ********************)


(** Defines the foreign support for DateTime
     Posits axioms for the basic data/operators, and 
     defines how they are extracted to ocaml (using helper functions
     defined in qcert/ocaml/...../Util.ml)
     *)

(* First we define a DATE_TIME_DURATION *)

Axiom DATE_TIME_DURATION : Set.
Extract Constant DATE_TIME_DURATION => "string".

Axiom DATE_TIME_DURATION_eq : DATE_TIME_DURATION -> DATE_TIME_DURATION -> bool.
Extract Inlined Constant DATE_TIME_DURATION_eq => "(fun x y -> x = y)".

Conjecture DATE_TIME_DURATION_eq_correct :
  forall f1 f2, (DATE_TIME_DURATION_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_DURATION_tostring : DATE_TIME_DURATION -> String.string.
Extract Inlined Constant DATE_TIME_DURATION_tostring => "(fun x -> Util.char_list_of_string x)".

Program Instance date_time_duration_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME_DURATION}.
Next Obligation.
  intros x y.
  case_eq (DATE_TIME_DURATION_eq x y); intros eqq.
  + left.
    f_equal.
    apply DATE_TIME_DURATION_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply DATE_TIME_DURATION_eq_correct in eqq2. 
    congruence.
Defined.
Next Obligation.
  exact True.
Defined.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  constructor.
  intros f.
  exact (DATE_TIME_DURATION_tostring f).
Defined.

(* Now we define a date/time. *)

Axiom DATE_TIME : Set.
Extract Constant DATE_TIME => "string".

Axiom DATE_TIME_eq : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_eq => "(fun x y -> x = y)".

Conjecture DATE_TIME_eq_correct :
  forall f1 f2, (DATE_TIME_eq f1 f2 = true <-> f1 = f2).

Axiom DATE_TIME_tostring : DATE_TIME -> String.string.
Extract Inlined Constant DATE_TIME_tostring => "(fun x -> Util.char_list_of_string x)".

Program Instance date_time_foreign_data : foreign_data
  := {foreign_data_type := DATE_TIME}.
Next Obligation.
  intros x y.
  case_eq (DATE_TIME_eq x y); intros eqq.
  + left.
    f_equal.
    apply DATE_TIME_eq_correct in eqq.
    trivial.
  + right; intros eqq2.
    red in eqq2.
    apply DATE_TIME_eq_correct in eqq2. 
    congruence.
Defined.
Next Obligation.
  exact True.
Defined.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  constructor.
  intros f.
  exact (DATE_TIME_tostring f).
Defined.

Axiom DATE_TIME_from_string : String.string -> DATE_TIME.
Extract Inlined Constant DATE_TIME_from_string => "(fun x -> Util.string_of_char_list x)".

Axiom DATE_TIME_DURATION_from_string : String.string -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_from_string => "(fun x -> Util.string_of_char_list x)".

Inductive date_time_component
  :=
  | date_time_DAY
  | date_time_MONTH
  | date_time_QUARTER
  | date_time_YEAR.

Definition date_time_component_tostring (part:date_time_component) : String.string
  := match part with
     | date_time_DAY => "day"
     | date_time_MONTH => "month"
     | date_time_QUARTER => "quarter"
     | date_time_YEAR => "year"
     end.

Global Instance date_time_component_to_string : ToString date_time_component
  := { toString := date_time_component_tostring }.

Axiom DATE_TIME_component : date_time_component -> DATE_TIME -> Z.
Extract Inlined Constant DATE_TIME_component => "(fun x y -> 0)".
  
Inductive date_time_unary_op
  :=
  | uop_date_time_component : date_time_component -> date_time_unary_op
  | uop_date_time_from_string
  | uop_date_time_duration_from_string
.

Local Open Scope string.

Definition date_time_unary_op_tostring (f:date_time_unary_op) : String.string
  := match f with
     | uop_date_time_component part =>
       "(dateTimeComponent" ++ (date_time_component_tostring part) ++ ")"
     | uop_date_time_from_string => "DateTimeFromString"
     | uop_date_time_duration_from_string => "DateTimeDurationFromString"
     end.

Require Import Qcert.Translation.ForeignToJava.
Require Import Qcert.Translation.NNRCtoJava.

Definition date_time_component_to_java_string (part:date_time_component): string
  := match part with
     | date_time_DAY => "UnaryOperators.day"
     | date_time_MONTH => "UnaryOperators.month"
     | date_time_QUARTER => "UnaryOperators.quarter"
     | date_time_YEAR => "UnaryOperators.year"
     end.

  
Definition date_time_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:date_time_unary_op)
             (d:java_json) : java_json
  := match fu with
     | uop_date_time_component part =>
       mk_java_unary_op1 "date_time_component" (date_time_component_to_java_string part) d
     | uop_date_time_from_string => mk_java_unary_op0 "date_time_from_string" d
     | uop_date_time_duration_from_string => mk_java_unary_op0 "date_time_duration_from_string" d
     end.

Definition date_time_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:date_time_unary_op)
             (d:String.string) : String.string
  := match fu with
     | uop_date_time_component part => "dateTimeComponent(" ++ quotel ++ (toString part) ++ quotel ++ ", " ++ d ++ ")"
     | uop_date_time_from_string => "dateTimeFromString(" ++ d ++ ")"
     | uop_date_time_duration_from_string => "dateTimeDurationFromString(" ++ d ++ ")"
     end.

Definition date_time_to_ajavascript_unary_op
             (fu:date_time_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | uop_date_time_component part =>
       call_runtime "dateTimeComponent" [ expr_literal (literal_string (toString part)); e ]
     | uop_date_time_from_string => call_runtime "dateTimeFromString" [ e ]
     | uop_date_time_duration_from_string => call_runtime "dateTimeDurationFromString" [ e ]
     end.

Axiom DATE_TIME_plus : DATE_TIME -> DATE_TIME_DURATION -> DATE_TIME.
Extract Inlined Constant DATE_TIME_plus => "(fun x y -> x)".

Axiom DATE_TIME_minus : DATE_TIME -> DATE_TIME_DURATION -> DATE_TIME.
Extract Inlined Constant DATE_TIME_minus => "(fun x y -> x)".

Axiom DATE_TIME_ne : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_ne => "(fun x y -> x <> y)".

Axiom DATE_TIME_lt : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_lt => "(fun x y -> x < y)".

Axiom DATE_TIME_le : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_le => "(fun x y -> x <= y)".

Axiom DATE_TIME_gt : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_gt => "(fun x y -> x > y)".

Axiom DATE_TIME_ge : DATE_TIME -> DATE_TIME -> bool.
Extract Inlined Constant DATE_TIME_ge => "(fun x y -> x >= y)".

Axiom DATE_TIME_DURATION_between : DATE_TIME -> DATE_TIME -> DATE_TIME_DURATION.
Extract Inlined Constant DATE_TIME_DURATION_between => "(fun x y -> """")".

Inductive date_time_binary_op
  :=
  | bop_date_time_plus
  | bop_date_time_minus
  | bop_date_time_ne
  | bop_date_time_lt
  | bop_date_time_le
  | bop_date_time_gt
  | bop_date_time_ge
  | bop_date_time_duration_between
.

Definition date_time_binary_op_tostring (f:date_time_binary_op) : String.string
  := match f with
     | bop_date_time_plus => "DateTimePlus"
     | bop_date_time_minus => "DateTimeMinus"
     | bop_date_time_ne => "DateTimeNe"
     | bop_date_time_lt => "DateTimeLt"
     | bop_date_time_le => "DateTimeLe"
     | bop_date_time_gt => "DateTimeGt"
     | bop_date_time_ge => "DateTimeGe"
     | bop_date_time_duration_between => "DateTimeDurationBetween"
     end.

(* Java equivalent: JavaScriptBackend.jsFunc *)
Definition jsFunc (name d1 d2:string)
  := name ++ "(" ++ d1 ++ ", " ++ d2 ++ ")".

Definition date_time_to_java_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:date_time_binary_op)
             (d1 d2:java_json) : java_json
  := match fb with
     | bop_date_time_plus => mk_java_binary_op0 "date_time_plus" d1 d2
     | bop_date_time_minus => mk_java_binary_op0 "date_time_minus" d1 d2
     | bop_date_time_ne =>  mk_java_binary_op0 "date_time_ne" d1 d2
     | bop_date_time_lt =>  mk_java_binary_op0 "date_time_lt" d1 d2
     | bop_date_time_le =>  mk_java_binary_op0 "date_time_le" d1 d2
     | bop_date_time_gt =>  mk_java_binary_op0 "date_time_gt" d1 d2
     | bop_date_time_ge => mk_java_binary_op0 "date_time_ge" d1 d2
     | bop_date_time_duration_between => mk_java_binary_op0 "date_time_duration_between" d1 d2

     end.

Definition date_time_to_javascript_binary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fb:date_time_binary_op)
             (d1 d2:String.string) : String.string
  := match fb with
     | bop_date_time_plus => jsFunc "dateTimePointPlus" d1 d2
     | bop_date_time_minus => jsFunc "dateTimePointMinus" d1 d2
     | bop_date_time_ne =>  jsFunc "dateTimePointNe" d1 d2
     | bop_date_time_lt =>  jsFunc "dateTimePointLt" d1 d2
     | bop_date_time_le =>  jsFunc "dateTimePointLe" d1 d2
     | bop_date_time_gt =>  jsFunc "dateTimePointGt" d1 d2
     | bop_date_time_ge => jsFunc "dateTimePointGe" d1 d2
     | bop_date_time_duration_between => jsFunc "dateTimeDurationBetween" d1 d2
     end.  

Definition date_time_to_ajavascript_binary_op
             (fb:date_time_binary_op)
             (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | bop_date_time_plus => call_runtime "dateTimePointPlus" [ e1; e2 ]
     | bop_date_time_minus => call_runtime "dateTimePointMinus" [ e1; e2 ]
     | bop_date_time_ne =>  call_runtime "dateTimePointNe" [ e1; e2 ]
     | bop_date_time_lt =>  call_runtime "dateTimePointLt" [ e1; e2 ]
     | bop_date_time_le =>  call_runtime "dateTimePointLe" [ e1; e2 ]
     | bop_date_time_gt =>  call_runtime "dateTimePointGt" [ e1; e2 ]
     | bop_date_time_ge => call_runtime "dateTimePointGe" [ e1; e2 ]
     | bop_date_time_duration_between => call_runtime "dateTimeDurationBetween" [ e1; e2 ]
     end.  

