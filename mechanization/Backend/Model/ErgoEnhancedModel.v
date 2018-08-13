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

Require Import List.
Require Import EquivDec.
Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.CommonSystem.
Require Import Qcert.Translation.ForeignToJava.
Require Import Qcert.Translation.ForeignToJavaScript.
Require Import Qcert.Translation.ForeignToJavaScriptAst.
Require Import Qcert.Translation.ForeignToScala.
Require Import Qcert.Common.DataModel.ForeignDataToJSON.
Require Import Qcert.Common.TypeSystem.ForeignTypeToJSON.
Require Import Qcert.Translation.ForeignToSpark.
Require Import Qcert.NNRCMR.Lang.ForeignReduceOps.
Require Import Qcert.Translation.ForeignToReduceOps.
Require Import Qcert.CldMR.Lang.ForeignCloudant.
Require Import Qcert.Translation.ForeignToCloudant.
Require Import Qcert.Compiler.Model.CompilerRuntime.
Require Import Qcert.Compiler.Model.CompilerModel.
Require Import Qcert.Compiler.Model.StringModelPart.
Require Qcert.NNRCMR.Lang.NNRCMR.
Require Qcert.CldMR.Lang.CldMR.
Require Import Qcert.Utils.OptimizerLogger.
Require Import String.
Require Import Qcert.cNRAEnv.Lang.cNRAEnv.
Require Import Qcert.NRAEnv.Lang.NRAEnv.
Require Import Qcert.cNNRC.Lang.cNNRC.
Require Import Qcert.NNRSimp.Lang.NNRSimp.
Require Import Qcert.DNNRC.Lang.DNNRCBase.
Require Import Qcert.tDNNRC.Lang.tDNNRC.
Require Import Qcert.DNNRC.Lang.Dataframe.

Require Import ErgoSpec.Backend.Model.DateTimeModelPart.

Import ListNotations.

Local Open Scope list_scope.

(* TODO: these should move *)
Definition check_subtype_pairs
           {br:brand_relation}
           {fr:foreign_type}
           (l:list (rtype*rtype)) : bool
  := forallb (fun τs => if subtype_dec (fst τs) (snd τs) then true else false) l.

Definition enforce_unary_op_schema
           {br:brand_relation}
           {fr:foreign_type}
           (ts1:rtype*rtype) (tr:rtype)
  : option (rtype*rtype)
  := if check_subtype_pairs (ts1::nil)
    then Some (tr, (snd ts1))
    else None.

Definition enforce_binary_op_schema
           {br:brand_relation}
           {fr:foreign_type}
           (ts1:rtype*rtype) (ts2:rtype*rtype) (tr:rtype)
  : option (rtype*rtype*rtype)
  := if check_subtype_pairs (ts1::ts2::nil)
    then Some (tr, (snd ts1), (snd ts2))
    else None.

Inductive enhanced_data : Set
  :=
  | enhancedstring : STRING -> enhanced_data
  | enhanceddateTime : DATE_TIME -> enhanced_data
  | enhanceddateTimeinterval : DATE_TIME_DURATION -> enhanced_data
.

Inductive enhanced_type : Set
  :=
  | enhancedTop : enhanced_type
  | enhancedBottom : enhanced_type
  | enhancedString : enhanced_type
  | enhancedDateTime : enhanced_type
  | enhancedDateTimeInterval : enhanced_type
.

Definition enhanced_type_to_string (et:enhanced_type) : string :=
  match et with
  | enhancedTop => "ETop"
  | enhancedBottom => "EBottom"
  | enhancedString => "EString"
  | enhancedDateTime => "EDateTime"
  | enhancedDateTimeInterval => "EDateTimeInterval"
  end.

Definition string_to_enhanced_type (s:string) : option enhanced_type :=
  match s with
  | "ETop"%string => Some enhancedTop
  | "EBottom"%string => Some enhancedBottom
  | "EString"%string => Some enhancedString
  | "EDateTime"%string => Some enhancedDateTime
  | "EDateTimeInterval"%string => Some enhancedDateTimeInterval
  | _ => None
  end.

Require Import RelationClasses.
Require Import Equivalence.

Existing Instance date_time_foreign_data.
Existing Instance date_time_duration_foreign_data.

Program Instance enhanced_foreign_data : foreign_data
  := mk_foreign_data enhanced_data _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - case_eq (STRING_eq s s0).
    + left; intros.
      f_equal.
      apply StringModelPart.STRING_eq_correct in H.
      trivial.
    + right; intros.
      inversion H0.
      apply StringModelPart.STRING_eq_correct in H2.
      congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_duration_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact True.
  - exact (@foreign_data_normalized date_time_foreign_data d).
  - exact (@foreign_data_normalized date_time_duration_foreign_data d).
Defined.
Next Obligation.
  destruct a.
  - simpl; trivial.
  - exact (@foreign_data_normalize_normalizes date_time_foreign_data d).
  - exact (@foreign_data_normalize_normalizes date_time_duration_foreign_data d).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (STRING_tostring s).
  - exact (@toString _ (@foreign_data_tostring date_time_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_duration_foreign_data) d).
Defined.

Definition denhanceddateTime td := dforeign (enhanceddateTime td).
Definition denhanceddateTimeinterval td := dforeign (enhanceddateTimeinterval td).

Require Import Qcert.Utils.JSON.

Axiom JENHANCED_string : STRING -> string.
Extract Constant JENHANCED_string => "(fun s -> Util.string_of_enhanced_string s)".

Definition jenhancedstring s := JENHANCED_string s.

Inductive enhanced_unary_op
  :=
  | enhanced_unary_date_time_op : date_time_unary_op -> enhanced_unary_op.

Definition onddateTime {A} (f : DATE_TIME -> A) (d : data) : option A
  := match d with
     | dforeign (enhanceddateTime fd) => Some (f fd)
     | _ => None
     end.

Definition ondstring {A} (f : String.string -> A) (d : data) : option A
  := match d with
     | dstring s => Some (f s)
     | _ => None
     end.

Definition date_time_unary_op_interp (op:date_time_unary_op) (d:data) : option data
  := match op with
     | uop_date_time_component part =>
       lift dnat (onddateTime (DATE_TIME_component part) d)
     | uop_date_time_from_string =>
       lift denhanceddateTime (ondstring DATE_TIME_from_string d)
     | uop_date_time_duration_from_string =>
       lift denhanceddateTimeinterval (ondstring DATE_TIME_DURATION_from_string d)
     end.


Definition enhanced_unary_op_interp
           (br:brand_relation_t)
           (op:enhanced_unary_op)
           (d:data) : option data
  := match op with
     | enhanced_unary_date_time_op f => date_time_unary_op_interp f d
     end.

Require Import String.

Program Instance enhanced_foreign_unary_op : foreign_unary_op
  := { foreign_unary_op_type := enhanced_unary_op
       ; foreign_unary_op_interp := enhanced_unary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
    decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (date_time_unary_op_tostring d).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct d0; simpl in H;
      unfold onddateTime, denhanceddateTime, denhanceddateTimeinterval, lift in H; simpl in H;
        destruct d; simpl in H; try discriminate.
    + destruct f; invcs H; repeat constructor.
    + invcs H; repeat constructor.
    + invcs H; repeat constructor.
Qed.

Inductive enhanced_binary_op
  :=
  | enhanced_binary_date_time_op : date_time_binary_op -> enhanced_binary_op
.

Definition onddateTime2 {A} (f : DATE_TIME -> DATE_TIME -> A) (d1 d2 : data) : option A
  := match d1, d2 with
     | dforeign (enhanceddateTime fd1), dforeign (enhanceddateTime fd2) => Some (f fd1 fd2)
     | _, _ => None
     end.

Definition rondbooldateTime2 (f: DATE_TIME -> DATE_TIME -> bool) (d1 d2:data) : option data
  := lift dbool (onddateTime2 f d1 d2).

Definition date_time_binary_op_interp
           (op:date_time_binary_op) (d1 d2:data) : option data
  := match op with
     | bop_date_time_plus
       => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeinterval td)
         => Some (denhanceddateTime (DATE_TIME_plus tp td))
       | _,_ => None
       end
     | bop_date_time_minus
       => match d1, d2 with
       | dforeign (enhanceddateTime tp), dforeign (enhanceddateTimeinterval td)
         => Some (denhanceddateTime (DATE_TIME_minus tp td))
       | _,_ => None
       end
     | bop_date_time_ne => rondbooldateTime2 DATE_TIME_ne d1 d2
     | bop_date_time_lt => rondbooldateTime2 DATE_TIME_lt d1 d2
     | bop_date_time_le => rondbooldateTime2 DATE_TIME_le d1 d2
     | bop_date_time_gt => rondbooldateTime2 DATE_TIME_gt d1 d2
     | bop_date_time_ge => rondbooldateTime2 DATE_TIME_ge d1 d2
     | bop_date_time_duration => lift denhanceddateTimeinterval (onddateTime2 DATE_TIME_DURATION_duration d1 d2)
     | bop_date_time_duration_days => lift dfloat (onddateTime2 DATE_TIME_DURATION_days d1 d2)
     | bop_date_time_duration_seconds => lift dfloat (onddateTime2 DATE_TIME_DURATION_seconds d1 d2)
     end.

Definition enhanced_binary_op_interp
           (br:brand_relation_t)
           (op:enhanced_binary_op)
           (d1 d2:data) : option data
  := match op with
     | enhanced_binary_date_time_op f => date_time_binary_op_interp f d1 d2
     end.

Program Instance enhanced_foreign_binary_op : foreign_binary_op
  := { foreign_binary_op_type := enhanced_binary_op
       ; foreign_binary_op_interp := enhanced_binary_op_interp }.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  - decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  destruct op.
  - exact (date_time_binary_op_tostring d).
Defined.
Next Obligation.
  destruct op; simpl in H.
  - destruct d; simpl in H;
      unfold rondbooldateTime2, onddateTime2, denhanceddateTime, lift in H
      ; destruct d1; simpl in H; try discriminate
      ; destruct f; simpl in H; try discriminate
      ; destruct d2; simpl in H; try discriminate
      ; try (destruct f; simpl in H; try discriminate)
      ; invcs H
      ; repeat constructor.
Qed.

Instance enhanced_foreign_runtime :
  foreign_runtime
  := mk_foreign_runtime
       enhanced_foreign_data
       enhanced_foreign_unary_op
       enhanced_foreign_binary_op.

(* TODO: fix me *)
Definition enhanced_to_java_data
           (quotel:String.string) (fd:enhanced_data) : java_json
  := match fd with
     | enhancedstring s => mk_java_json (STRING_tostring s)
     | enhanceddateTime tp => mk_java_json (@toString _ date_time_foreign_data.(@foreign_data_tostring ) tp)
     | enhanceddateTimeinterval tp => mk_java_json (@toString _ date_time_duration_foreign_data.(@foreign_data_tostring ) tp)
     end.

Definition enhanced_to_java_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:enhanced_unary_op)
             (d:java_json) : java_json
  := match fu with
     | enhanced_unary_date_time_op op =>
       date_time_to_java_unary_op indent eol quotel op d
     end.

Definition enhanced_to_java_binary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fb:enhanced_binary_op)
           (d1 d2:java_json) : java_json
  := match fb with
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

Definition enhanced_to_javascript_data
           (quotel:String.string) (fd:enhanced_data) : String.string
  := match fd with
     | enhancedstring s => STRING_tostring s
     | enhanceddateTime tp => (@toString _ date_time_foreign_data.(@foreign_data_tostring ) tp)
     | enhanceddateTimeinterval tp => (@toString _ date_time_duration_foreign_data.(@foreign_data_tostring ) tp)
     end.

(* Java equivalent: JavaScriptBackend.foreign_to_javascript_unary_op *)
Definition enhanced_to_javascript_unary_op
             (indent:nat) (eol:String.string)
             (quotel:String.string) (fu:enhanced_unary_op)
             (d:String.string) : String.string
  := match fu with
     | enhanced_unary_date_time_op op =>
       date_time_to_javascript_unary_op indent eol quotel op d
     end.

(* Java equivalent: JavaScriptBackend.foreign_to_javascript_binary_op *)
Definition enhanced_to_javascript_binary_op
           (indent:nat) (eol:String.string)
           (quotel:String.string) (fb:enhanced_binary_op)
           (d1 d2:String.string) : String.string
  := match fb with
     | enhanced_binary_date_time_op op =>
       date_time_to_javascript_binary_op indent eol quotel op d1 d2
     end.

Definition enhanced_to_ajavascript_unary_op
             (fu:enhanced_unary_op)
             (e:JsSyntax.expr) : JsSyntax.expr
  := match fu with
     | enhanced_unary_date_time_op op =>
       date_time_to_ajavascript_unary_op op e
     end.

Definition enhanced_to_ajavascript_binary_op
           (fb:enhanced_binary_op)
           (e1 e2:JsSyntax.expr) : JsSyntax.expr
  := match fb with
     | enhanced_binary_date_time_op op =>
       date_time_to_ajavascript_binary_op op e1 e2
     end.

Instance enhanced_foreign_to_javascript :
  @foreign_to_javascript enhanced_foreign_runtime
  := mk_foreign_to_javascript
       enhanced_foreign_runtime
       enhanced_to_javascript_unary_op
       enhanced_to_javascript_binary_op.

Instance enhanced_foreign_to_ajavascript :
  @foreign_to_ajavascript enhanced_foreign_runtime
  := mk_foreign_to_ajavascript
       enhanced_foreign_runtime
       enhanced_to_ajavascript_unary_op
       enhanced_to_ajavascript_binary_op.

Definition enhanced_to_scala_unary_op (op: enhanced_unary_op) (d: string) : string :=
  match op with
    | enhanced_unary_date_time_op op => "EnhancedModel: date time ops not supported for now."
  end.

Definition enhanced_to_scala_spark_datatype {ftype: foreign_type} (ft: foreign_type_type) : string :=
  "FloatType".

Instance enhanced_foreign_to_scala {ftype: foreign_type}:
  @foreign_to_scala enhanced_foreign_runtime _
  := mk_foreign_to_scala
       enhanced_foreign_runtime _
       enhanced_to_scala_unary_op
       enhanced_to_scala_spark_datatype.

(* TODO: add general support for "tagged" stuff in JSON.
    Like our left/right encoding.  so that we can use it for
    timescale/timepoint.  just using a string may work for now.
*)



Program Instance enhanced_foreign_to_JSON : foreign_to_JSON
  := mk_foreign_to_JSON enhanced_foreign_data _ _.
Next Obligation.
  (* TODO: For now, we assume that JSON supports floating point *)
  exact None.
Defined.
Next Obligation.
  destruct fd.
  - exact (jstring (jenhancedstring s)).
  - exact (jstring (@toString _ date_time_foreign_data.(@foreign_data_tostring ) d)).
  - exact (jstring (@toString _ date_time_duration_foreign_data.(@foreign_data_tostring ) d)).
Defined.

  Inductive enhanced_numeric_type :=
  | enhanced_numeric_int
  | enhanced_numeric_float.

  Global Instance enhanced_numeric_type_eqdec : EqDec enhanced_numeric_type eq.
  Proof.
    red. unfold equiv, complement.
    change (forall x y : enhanced_numeric_type, {x = y} + {x <> y}).
    decide equality.
  Defined.

  Definition enhanced_to_cld_numeric_type
             (typ:enhanced_numeric_type) : CldMR.cld_numeric_type
    := match typ with
       | enhanced_numeric_int => CldMR.Cld_int
       | enhanced_numeric_float => CldMR.Cld_float
       end.

Inductive enhanced_reduce_op
  := RedOpCount : enhanced_reduce_op
   | RedOpSum (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMin (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpMax (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpArithMean (typ:enhanced_numeric_type) : enhanced_reduce_op
   | RedOpStats (typ:enhanced_numeric_type) : enhanced_reduce_op.

Definition enhanced_numeric_type_prefix
           (typ:enhanced_numeric_type) : string
  := match typ with
     | enhanced_numeric_int => ""%string
     | enhanced_numeric_float => "F"%string
     end.

Definition enhanced_reduce_op_tostring (op:enhanced_reduce_op) : string
  := match op with
     | RedOpCount => "COUNT"%string
     | RedOpSum typ => append (enhanced_numeric_type_prefix typ) "FSUM"%string
     | RedOpMin typ  => append (enhanced_numeric_type_prefix typ) "FMIN"%string
     | RedOpMax typ => append (enhanced_numeric_type_prefix typ) "FMAX"%string
     | RedOpArithMean typ => append (enhanced_numeric_type_prefix typ) "FARITHMEAN"%string
     | RedOpStats typ => append (enhanced_numeric_type_prefix typ) "FSTATS"%string
     end.

Definition enhanced_numeric_sum (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatSum
     | enhanced_numeric_float
       => OpFloatSum
     end.

Definition enhanced_numeric_min (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMin
     | enhanced_numeric_float
       => OpFloatBagMin
     end.

Definition enhanced_numeric_max (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMax
     | enhanced_numeric_float
       => OpFloatBagMax
     end.

Definition enhanced_numeric_arith_mean (typ:enhanced_numeric_type) : unary_op
  := match typ with
     | enhanced_numeric_int
       => OpNatMean
     | enhanced_numeric_float
       => OpFloatMean
     end.

Definition enhanced_reduce_op_interp
           (br:brand_relation_t)
           (op:enhanced_reduce_op)
           (dl:list data) : option data
  := match op with
      | RedOpCount | RedOpSum _ | RedOpMin _ | RedOpMax _ | RedOpArithMean _ =>
        let uop :=
            match op with
            | RedOpCount  => OpCount
            | RedOpSum typ => enhanced_numeric_sum typ
            | RedOpMin typ => enhanced_numeric_min typ
            | RedOpMax typ => enhanced_numeric_max typ
            | RedOpArithMean typ => enhanced_numeric_arith_mean typ
            | RedOpStats _ => OpCount (* assert false *)
            end
        in
        unary_op_eval br uop (dcoll dl) 
      | RedOpStats typ =>
        let coll := dcoll dl in
        let count := unary_op_eval br OpCount coll in
        let sum := unary_op_eval br (enhanced_numeric_sum typ) coll in
        let min := unary_op_eval br (enhanced_numeric_min typ) coll in
        let max := unary_op_eval br (enhanced_numeric_max typ) coll in
        let v :=
            match (count, sum, min, max) with
              | (Some count, Some sum, Some min, Some max) =>
                Some (drec (("count"%string, count)
                              ::("max"%string, max)
                              ::("min"%string, min)
                              ::("sum"%string, sum)
                              ::nil))
              | _ => None
            end
        in
        v
     end.

Program Instance enhanced_foreign_reduce_op : foreign_reduce_op
  := mk_foreign_reduce_op enhanced_foreign_data enhanced_reduce_op _ _ enhanced_reduce_op_interp _.
Next Obligation.
  red; unfold equiv, complement.
  change (forall x y:enhanced_reduce_op, {x = y} + {x <> y}).
  decide equality; decide equality.
Defined.
Next Obligation.
  constructor.
  apply enhanced_reduce_op_tostring.
Defined.
Next Obligation.
  destruct op; simpl in *; invcs H.
  - constructor.
  - destruct typ; simpl in *.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_min in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmin in *.
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + unfold lifted_max in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
    + unfold lifted_fmax in * .
      apply some_lift in H2; destruct H2 as [? eqq ?];
        subst; constructor.
  - destruct typ; simpl in *.
    + destruct (dsum dl); simpl in *; try discriminate.
      unfold lifted_min, lifted_max in *.
      destruct ((lift bnummin (lifted_zbag dl))); simpl in *; try discriminate.
      destruct ((lift bnummax (lifted_zbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
      * reflexivity.
    + case_eq (lifted_fsum dl); intros; simpl in *; rewrite H in *; try discriminate.
      unfold lifted_fmin, lifted_fmax in *.
      destruct ((lift float_list_min (lifted_fbag dl))); simpl in *; try discriminate.
      destruct ((lift float_list_max (lifted_fbag dl))); simpl in *; try discriminate.
      invcs H2.
      constructor.
      * repeat constructor.
        apply some_lift in H; destruct H as [? eqq ?]; subst.
        constructor.
      * reflexivity.
Qed.

Definition enhanced_to_reduce_op (uop:unary_op) : option NNRCMR.reduce_op
  := match uop with
     | OpCount => Some (NNRCMR.RedOpForeign RedOpCount)
     | OpNatSum =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int))
     | OpFloatSum =>
       Some (NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float))
     | OpNatMin =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int))
     | OpFloatBagMin =>
       Some (NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float))
     | OpNatMax =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int))
     | OpFloatBagMax =>
       Some (NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float))
     | OpNatMean =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int))
     | OpFloatMean =>
       Some (NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float))
     | _ => None
     end.

Definition enhanced_of_reduce_op (rop:NNRCMR.reduce_op) : option unary_op
  := match rop with
     | NNRCMR.RedOpForeign RedOpCount => Some OpCount
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_int) =>
       Some (OpNatSum)
     | NNRCMR.RedOpForeign (RedOpSum enhanced_numeric_float) =>
       Some (OpFloatSum)
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_int) =>
       Some (OpNatMin)
     | NNRCMR.RedOpForeign (RedOpMin enhanced_numeric_float) =>
       Some (OpFloatBagMin)
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_int) =>
       Some (OpNatMax)
     | NNRCMR.RedOpForeign (RedOpMax enhanced_numeric_float) =>
       Some (OpFloatBagMax)
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_int) =>
       Some (OpNatMean)
     | NNRCMR.RedOpForeign (RedOpArithMean enhanced_numeric_float) =>
       Some (OpFloatMean)
     | NNRCMR.RedOpForeign (RedOpStats _) =>
       None (* XXX TODO? XXX *)
     end.

Program Instance enhanced_foreign_to_reduce_op : foreign_to_reduce_op
  := mk_foreign_to_reduce_op enhanced_foreign_runtime enhanced_foreign_reduce_op enhanced_to_reduce_op _ enhanced_of_reduce_op _.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct uop; simpl in *; invcs H; try reflexivity.
Qed.
Next Obligation.
  unfold NNRCMR.reduce_op_eval.
  destruct rop; simpl in *; invcs H; try reflexivity.
  destruct f; invcs H1; simpl; try reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
  destruct typ; invcs H0; reflexivity.
Qed.

Local Open Scope string_scope.
Definition enhanced_to_spark_reduce_op
           (rop:enhanced_reduce_op)
           (scala_endl quotel:string) : string
  := match rop with
      | RedOpCount => ".count().toString()"
      | RedOpSum enhanced_numeric_int => ".aggregate(0)(_ + _.toInt, _ + _).toString()"
      | RedOpSum enhanced_numeric_float => ".aggregate(0.0)(_ + _.toDouble, _ + _).toString()"
      | RedOpMin enhanced_numeric_int => ".aggregate(Int.MaxValue)(((x, y) => Math.min(x, y.toInt)), Math.min).toString()"
      | RedOpMin enhanced_numeric_float => ".aggregate(Double.MaxValue)(((x, y) => Math.min(x, y.toDouble)), Math.min).toString()"
      | RedOpMax enhanced_numeric_int =>
        ".aggregate(Int.MinValue)(((x, y) => Math.max(x, y.toInt)), Math.max).toString()"
      | RedOpMax enhanced_numeric_float =>
        ".aggregate(Double.MinValue)(((x, y) => Math.max(x, y.toDouble)), Math.max).toString()"
      | RedOpStats _ =>
        ".aggregate("""")(statsReduce, statsRereduce).toString()" ++ scala_endl ++
                     "  sc.parallelize(Array(res))"
      | RedOpArithMean _ => (* assert false *)
        ".arithmean /* ArithMean must be removed before code generation */"
     end.

(* NNRCMR rewrites *)
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Qcert.NNRCMR.NNRCMRRuntime.
Require Import Qcert.NNRCMR.Optim.NNRCMRRewrite.

  (* Java equivalent: MROptimizer.min_max_to_stats *)
  Definition min_max_to_stats avoid (mr: mr) :=
    match mr.(mr_reduce) with
    | RedOp (RedOpForeign op) =>
      match op with
      | RedOpMin typ | RedOpMax typ =>
        let stats_field :=
            match op with
            | RedOpMin _ => "min"%string
            | RedOpMax _ => "max"%string
            | _ => "ERROR"%string (* assert false *)
            end
        in
        let (tmp, avoid) := fresh_mr_var "stats$" avoid in
        let mr1 :=
           mkMR
             mr.(mr_input)
             tmp
             mr.(mr_map)
             (RedOp (RedOpForeign (RedOpStats typ)))
        in
        let x := "stats"%string in
        let mr2 :=
            mkMR
              tmp
              mr.(mr_output)
              (MapScalar (x, NNRCUnop OpBag (NNRCUnop (OpDot stats_field) (NNRCVar x))))
              RedSingleton
        in
        Some (mr1::mr2::nil)
      | _ => None
      end
    | _ => None
    end.

  (* Java equivalent: MROptimizer.arithmean_to_stats *)
  Definition arithmean_to_stats avoid (mr: mr) :=
    match mr.(mr_reduce) with
    | RedOp (RedOpForeign op) =>
      match op with
      | RedOpArithMean typ =>
        let (tmp, avoid) := fresh_mr_var "stats$" avoid in
        let mr1 :=
           mkMR
             mr.(mr_input)
             tmp
             mr.(mr_map)
             (RedOp (RedOpForeign (RedOpStats typ)))
        in
        let map :=
            match typ with
            | enhanced_numeric_int =>
              let zero := NNRCConst (dnat 0) in
              let x := "stats"%string in
              MapScalar (x, NNRCUnop OpBag
                                    (NNRCIf (NNRCBinop OpEqual (NNRCUnop (OpDot "count"%string) (NNRCVar x)) zero)
                                           zero
                                           (NNRCBinop (OpNatBinary NatDiv)
                                                     (NNRCUnop (OpDot "sum"%string) (NNRCVar x))
                                                     (NNRCUnop (OpDot "count"%string) (NNRCVar x)))))
            | enhanced_numeric_float =>
              let zero := NNRCConst (dnat 0) in
              let zerof := NNRCConst (dfloat float_zero) in
              let x := "stats"%string in
              MapScalar (x, NNRCUnop OpBag
                                    (NNRCIf (NNRCBinop OpEqual (NNRCUnop (OpDot "count"%string) (NNRCVar x)) zero)
                                           zerof
                                           (NNRCBinop (OpFloatBinary FloatDiv)
                                                     (NNRCUnop (OpDot "sum"%string) (NNRCVar x))
                                                     (NNRCUnop (OpFloatOfNat)
                                                       (NNRCUnop (OpDot "count"%string) (NNRCVar x))))))
            end
        in
        let mr2 :=
            mkMR
              tmp
              mr.(mr_output)
              map
              RedSingleton
        in
        Some (mr1::mr2::nil)
      | _ => None
      end
    | _ => None
    end.

  Definition min_max_free_reduce (src:reduce_fun)
    := match src with
       | RedOp (RedOpForeign (RedOpMin _|RedOpMax _)) => False
       | _ => True
       end.

  Definition arithmean_free_reduce (src:reduce_fun)
    := match src with
       | RedOp (RedOpForeign (RedOpArithMean _)) => False
       | _ => True
       end.

  Definition min_max_free_mr (src:mr)
    := min_max_free_reduce src.(mr_reduce).

  Definition arithmean_free_mr (src:mr)
    := arithmean_free_reduce src.(mr_reduce).

  Definition min_max_free_mr_chain (src:list mr)
    := Forall min_max_free_mr src.

  Definition min_max_free_nnrcmr (src:nnrcmr)
    := min_max_free_mr_chain src.(mr_chain).

  Definition arithmean_free_mr_chain (src:list mr)
    := Forall arithmean_free_mr src.

  Definition arithmean_free_nnrcmr (src:nnrcmr)
    := arithmean_free_mr_chain src.(mr_chain).

  Definition to_spark_nnrcmr (l: nnrcmr) :=
    let avoid := get_nnrcmr_vars l in
    let l := apply_rewrite (arithmean_to_stats avoid) l in
    l.

  Definition to_spark_nnrcmr_prepared (src:nnrcmr)
    := arithmean_free_nnrcmr src.

Program Instance enhanced_foreign_to_spark : foreign_to_spark
  := mk_foreign_to_spark
       enhanced_foreign_runtime
       enhanced_foreign_reduce_op
       enhanced_to_spark_reduce_op
       to_spark_nnrcmr.

Instance enhanced_foreign_cloudant : foreign_cloudant
  := mk_foreign_cloudant
       enhanced_foreign_runtime
       (OpFloatSum)
       (OpFloatBagMin)
       (OpFloatBagMax).

Definition enhanced_to_cloudant_reduce_op
           (rop:enhanced_reduce_op) : CldMR.cld_reduce_op
  := match rop with
     | RedOpCount => CldMR.CldRedOpCount
     | RedOpSum typ => CldMR.CldRedOpSum (enhanced_to_cld_numeric_type typ)
     | RedOpStats typ => CldMR.CldRedOpStats (enhanced_to_cld_numeric_type typ)
     | RedOpMin _ => CldMR.CldRedOpStats CldMR.Cld_int (* assert false *)
     | RedOpMax _ => CldMR.CldRedOpStats CldMR.Cld_int (* assert false *)
     | RedOpArithMean _ => CldMR.CldRedOpStats CldMR.Cld_int (* assert false *)
     end.

  (* Java equivalent: MROptimizer.foreign_to_cloudant_prepare_nnrcmr *)
  Definition to_cloudant_nnrcmr (l: nnrcmr) :=
    let avoid := get_nnrcmr_vars l in
    let l := apply_rewrite (min_max_to_stats avoid) l in
    let l := apply_rewrite (arithmean_to_stats avoid) l in
    l.

  Definition to_cloudant_nnrcmr_prepared (src:nnrcmr)
    := min_max_free_nnrcmr src /\ arithmean_free_nnrcmr src.

  Program Instance enhanced_foreign_to_cloudant : foreign_to_cloudant
    :=
      { foreign_to_cloudant_reduce_op := enhanced_to_cloudant_reduce_op
        ; foreign_to_cloudant_prepare_nnrcmr := to_cloudant_nnrcmr
        ; foreign_to_cloudant_nnrcmr_prepared := to_cloudant_nnrcmr_prepared
      }.
  Next Obligation.
    unfold to_cloudant_nnrcmr.
    unfold to_cloudant_nnrcmr_prepared.
    unfold min_max_free_nnrcmr, min_max_free_mr_chain, min_max_free_mr, min_max_free_reduce.
    split.
    - unfold apply_rewrite, min_max_to_stats.
      unfold mr_chain_apply_rewrite.
      apply Forall_forall; intros ? inn.
      simpl in *.
      apply in_flat_map in inn.
      destruct inn as [? [inn1 inn2]].
      destruct x; simpl.
      destruct mr_reduce; simpl in *;
        unfold min_max_free_mr;
        simpl;
      trivial.
      destruct r; simpl in *; trivial.
      destruct x0; simpl in *.
      destruct mr_reduce; simpl in *;
        try solve [invcs inn2; invcs H].
      destruct r; simpl in * .
      destruct f0; simpl in *.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + apply in_flat_map in inn1.
        destruct inn1 as [? [inn1 inn3]].
        destruct x.
        simpl in inn3.
        destruct mr_reduce
        ; try solve [simpl in inn3; intuition
                     ; invcs H].
        destruct r; destruct f0
        ; simpl in inn3; intuition
        ; invcs H0
        ; try solve [invcs H | invcs H1].
      + apply in_flat_map in inn1.
        destruct inn1 as [? [inn1 inn3]].
        destruct x.
        simpl in inn3.
        destruct mr_reduce
        ; try solve [simpl in inn3; intuition
                     ; invcs H].
        destruct r; destruct f0
        ; simpl in inn3; intuition
        ; invcs H0
        ; try solve [invcs H | invcs H1].
      + intuition.
        invcs H; trivial.
        intuition.
        invcs H0; trivial.
      + intuition.
        invcs H; trivial.
    - unfold apply_rewrite, mr_chain_apply_rewrite, arithmean_free_nnrcmr, arithmean_free_mr_chain.
      simpl in *.
      apply Forall_forall; intros ? inn.
      apply in_flat_map in inn.
      destruct inn as [? [inn1 inn2]].
      destruct x; simpl.
      destruct mr_reduce; simpl in *;
        unfold arithmean_free_mr;
        simpl;
      trivial.
      destruct r; simpl in *; trivial.
      destruct x0; simpl in *.
      destruct mr_reduce; simpl in *;
        try solve [invcs inn2; invcs H].
      destruct r; simpl in * .
      destruct f0; simpl in *.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
      + intuition.
        invcs H; trivial.
        invcs H0; trivial.
      + intuition.
        invcs H; trivial.
  Qed.

  (* nra optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nraenv_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_nraenv_token_type => "Util.nra_logger_token_type".

  Axiom OPTIMIZER_LOGGER_nraenv_startPass :
    String.string -> nraenv -> OPTIMIZER_LOGGER_nraenv_token_type.

  Extract Constant OPTIMIZER_LOGGER_nraenv_startPass =>
  "(fun name input -> Logger.nra_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nraenv_step :
    OPTIMIZER_LOGGER_nraenv_token_type -> String.string ->
    nraenv -> nraenv ->
    OPTIMIZER_LOGGER_nraenv_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_step =>
  "(fun token name input output -> Logger.nra_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nraenv_endPass :
    OPTIMIZER_LOGGER_nraenv_token_type -> nraenv -> OPTIMIZER_LOGGER_nraenv_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_endPass =>
  "(fun token output -> Logger.nra_log_endPass token output)".

  Instance foreign_nraenv_optimizer_logger :
    optimizer_logger string nraenv
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nraenv_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nraenv_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nraenv_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nraenv_endPass
      } .

  (* nrc optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nnrc_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_nnrc_token_type => "Util.nrc_logger_token_type".

  Axiom OPTIMIZER_LOGGER_nnrc_startPass :
    String.string -> nnrc -> OPTIMIZER_LOGGER_nnrc_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_startPass =>
  "(fun name input -> Logger.nrc_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nnrc_step :
    OPTIMIZER_LOGGER_nnrc_token_type -> String.string ->
    nnrc -> nnrc ->
    OPTIMIZER_LOGGER_nnrc_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_step =>
  "(fun token name input output -> Logger.nrc_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nnrc_endPass :
    OPTIMIZER_LOGGER_nnrc_token_type -> nnrc -> OPTIMIZER_LOGGER_nnrc_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_endPass =>
  "(fun token output -> Logger.nrc_log_endPass token output)".

    Instance foreign_nnrc_optimizer_logger :
    optimizer_logger string nnrc
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrc_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrc_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrc_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrc_endPass
      } .

    (* nnrs_imp optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_nnrs_imp_expr_token_type => "Util.nnrs_imp_expr_logger_token_type".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_startPass :
    String.string -> nnrs_imp_expr -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_startPass =>
  "(fun name input -> Logger.nnrs_imp_expr_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_step :
    OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> String.string ->
    nnrs_imp_expr -> nnrs_imp_expr ->
    OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_step =>
  "(fun token name input output -> Logger.nnrs_imp_expr_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> nnrs_imp_expr -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_endPass =>
  "(fun token output -> Logger.nnrs_imp_expr_log_endPass token output)".

    Instance foreign_nnrs_imp_expr_optimizer_logger :
    optimizer_logger string nnrs_imp_expr
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_expr_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_expr_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_expr_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_expr_endPass
      } .

  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type => "Util.nnrs_imp_stmt_logger_token_type".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass :
    String.string -> nnrs_imp_stmt -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass =>
  "(fun name input -> Logger.nnrs_imp_stmt_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_step :
    OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> String.string ->
    nnrs_imp_stmt -> nnrs_imp_stmt ->
    OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_step =>
  "(fun token name input output -> Logger.nnrs_imp_stmt_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> nnrs_imp_stmt -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass =>
  "(fun token output -> Logger.nnrs_imp_stmt_log_endPass token output)".

    Instance foreign_nnrs_imp_stmt_optimizer_logger :
    optimizer_logger string nnrs_imp_stmt
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass
      } .

      Axiom OPTIMIZER_LOGGER_nnrs_imp_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_nnrs_imp_token_type => "Util.nnrs_imp_logger_token_type".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_startPass :
    String.string -> nnrs_imp -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_startPass =>
  "(fun name input -> Logger.nnrs_imp_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_step :
    OPTIMIZER_LOGGER_nnrs_imp_token_type -> String.string ->
    nnrs_imp -> nnrs_imp ->
    OPTIMIZER_LOGGER_nnrs_imp_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_step =>
  "(fun token name input output -> Logger.nnrs_imp_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_nnrs_imp_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_token_type -> nnrs_imp -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_endPass =>
  "(fun token output -> Logger.nnrs_imp_log_endPass token output)".

    Instance foreign_nnrs_imp_optimizer_logger :
    optimizer_logger string nnrs_imp
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_nnrs_imp_token_type
        ; logStartPass := OPTIMIZER_LOGGER_nnrs_imp_startPass
        ; logStep :=  OPTIMIZER_LOGGER_nnrs_imp_step
        ; logEndPass :=  OPTIMIZER_LOGGER_nnrs_imp_endPass
      } .

(** Foreign typing, used to build the basic_model *)

Definition enhanced_type_join (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedBottom, _ => t2
     | _, enhancedBottom => t1
     | enhancedString, enhancedString => enhancedString
     | enhancedDateTime, enhancedDateTime => enhancedDateTime
     | enhancedDateTimeInterval, enhancedDateTimeInterval => enhancedDateTimeInterval
     | _, _ => enhancedTop
     end.

Definition enhanced_type_meet (t1 t2:enhanced_type)
  := match t1, t2 with
     | enhancedTop, _ => t2
     | _, enhancedTop => t1
     | enhancedString, enhancedString => enhancedString
     | enhancedDateTime, enhancedDateTime => enhancedDateTime
     | enhancedDateTimeInterval, enhancedDateTimeInterval => enhancedDateTimeInterval
     | _, _ => enhancedBottom
     end.

Inductive enhanced_subtype : enhanced_type -> enhanced_type -> Prop :=
| enhanced_subtype_top t : enhanced_subtype t enhancedTop
| enhanced_subtype_bottom t : enhanced_subtype enhancedBottom t
| enhanced_subtype_refl t : enhanced_subtype t t.

Instance enhanced_subtype_pre : PreOrder enhanced_subtype.
Proof.
  constructor; red; intros.
  - destruct x; constructor.
  - inversion H; inversion H0; subst; try constructor; congruence.
Qed.

Instance enhanced_subtype_post : PartialOrder eq enhanced_subtype.
Proof.
  intros x y; split.
  - intros; subst.
    repeat red.
    split; constructor.
  - destruct 1.
    inversion H; inversion H0; congruence.
Qed.

Instance enhanced_type_lattice : Lattice enhanced_type eq
  := {
      join := enhanced_type_join
      ; meet := enhanced_type_meet
    }.
Proof.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
    reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
    reflexivity.
  - red; intros t1.
    simpl.
    destruct t1; simpl; try reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
    reflexivity.
  - red; intros t1 t2 t3.
    destruct t1; destruct t2; destruct t3; simpl;
    reflexivity.
  - red; intros t1.
    destruct t1; simpl;
    reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
  - red; intros t1 t2.
    destruct t1; destruct t2; simpl;
      reflexivity.
Defined.

Instance enhanced_type_olattice : OLattice eq enhanced_subtype.
Proof.
  constructor.
  split.
  - destruct a; destruct b; inversion 1; simpl; reflexivity.
  - destruct a; destruct b; inversion 1; simpl;
    constructor.
Qed.

Program Instance enhanced_foreign_type : foreign_type
  := mk_foreign_type enhanced_type _ _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  intros.
  change ({x = y} + {x <> y}).
  decide equality.
Defined.
Next Obligation.
  destruct a; destruct b; try solve [left; constructor | right; inversion 1].
Defined.

Program Instance enhanced_foreign_type_to_JSON : foreign_type_to_JSON
  := mk_foreign_type_to_JSON enhanced_foreign_type _ _.
Next Obligation.
  exact (string_to_enhanced_type s).
Defined.
Next Obligation.
  exact (enhanced_type_to_string fd).
Defined.

Inductive enhanced_has_type : enhanced_data -> enhanced_type -> Prop :=
| enhanced_has_type_top fd : enhanced_has_type fd enhancedTop
| enhanced_has_type_string (s:STRING) : enhanced_has_type (enhancedstring s) enhancedString
| enhanced_has_type_dateTime (tp:DATE_TIME) : enhanced_has_type (enhanceddateTime tp) enhancedDateTime
| enhanced_has_type_dateTimeinterval (tp:DATE_TIME_DURATION) : enhanced_has_type (enhanceddateTimeinterval tp) enhancedDateTimeInterval
.

Definition enhanced_infer_type (d:enhanced_data) : option enhanced_type
  := match d with
     | enhancedstring _ => Some enhancedString
     | enhanceddateTime _ => Some enhancedDateTime
     | enhanceddateTimeinterval _ => Some enhancedDateTimeInterval
     end.

Program Instance enhanced_foreign_data_typing :
  @foreign_data_typing enhanced_foreign_data enhanced_foreign_type
  := mk_foreign_data_typing
       enhanced_foreign_data
       enhanced_foreign_type
       enhanced_has_type _ _ _
       enhanced_infer_type _ _ _
.
Next Obligation.
  inversion H; subst;
    simpl; trivial.
  - destruct d; simpl; constructor.
  - constructor.
  - constructor.
Defined.
Next Obligation.
  inversion H0; subst; simpl.
  - constructor.
  - inversion H.
  - trivial.
Defined.
Next Obligation.
  inversion H; inversion H0; subst; simpl; try constructor; congruence.
Defined.
Next Obligation.
  destruct d; simpl; eexists; reflexivity.
Defined.
Next Obligation.
  destruct d; simpl in H; invcs H; constructor.
Defined.
Next Obligation.
  destruct d; simpl in H, H0
  ; invcs H; invcs H0; constructor.
Defined.

Definition dnnrc_for_log {br:brand_relation}
  := (@dnnrc_base enhanced_foreign_runtime (type_annotation unit) dataframe).

  (* dnnrc optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_dnnrc_token_type : Set.
  Extract Constant OPTIMIZER_LOGGER_dnnrc_token_type => "Util.dnrc_logger_token_type".

  Axiom OPTIMIZER_LOGGER_dnnrc_startPass :
    forall {br:brand_relation}, String.string -> dnnrc_for_log -> OPTIMIZER_LOGGER_dnnrc_token_type.

  Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_startPass =>
  "(fun br name input -> Logger.dnrc_log_startPass (Util.string_of_char_list name) input)".

  Axiom OPTIMIZER_LOGGER_dnnrc_step :
    forall  {br:brand_relation}, 
    OPTIMIZER_LOGGER_dnnrc_token_type -> String.string ->
    dnnrc_for_log -> dnnrc_for_log ->
    OPTIMIZER_LOGGER_dnnrc_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_step =>
  "(fun br token name input output -> Logger.dnrc_log_step token (Util.string_of_char_list name) input output)".

  Axiom OPTIMIZER_LOGGER_dnnrc_endPass :
    forall {br:brand_relation}, OPTIMIZER_LOGGER_dnnrc_token_type -> dnnrc_for_log -> OPTIMIZER_LOGGER_dnnrc_token_type.
  
  Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_endPass =>
  "(fun br token output -> Logger.dnrc_log_endPass token output)".

  Instance foreign_dnnrc_optimizer_logger  {br:brand_relation} :
    optimizer_logger string dnnrc_for_log
    :=
      {
        optimizer_logger_token_type := OPTIMIZER_LOGGER_dnnrc_token_type
        ; logStartPass := OPTIMIZER_LOGGER_dnnrc_startPass
        ; logStep :=  OPTIMIZER_LOGGER_dnnrc_step
        ; logEndPass :=  OPTIMIZER_LOGGER_dnnrc_endPass
      } .

Module EnhancedRuntime <: CompilerRuntime.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_foreign_runtime : foreign_runtime
    := enhanced_foreign_runtime.
  Definition compiler_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_foreign_to_javascript : foreign_to_javascript
    := enhanced_foreign_to_javascript.
  Definition compiler_foreign_to_ajavascript : foreign_to_ajavascript
    := enhanced_foreign_to_ajavascript.
  Definition compiler_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_foreign_to_JSON : foreign_to_JSON
    := enhanced_foreign_to_JSON.
  Definition compiler_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_foreign_cloudant : foreign_cloudant
    := enhanced_foreign_cloudant.
  Definition compiler_foreign_to_cloudant : foreign_to_cloudant
    := enhanced_foreign_to_cloudant.
  Definition compiler_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedRuntime.

Definition DateTime {br:brand_relation} : rtype := Foreign enhancedDateTime.
Definition DateTimeInterval {br:brand_relation} : rtype := Foreign enhancedDateTimeInterval.

Definition isDateTime {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTime => true
  | _ => false
  end.

Definition isDateTimeInterval {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Foreign₀ enhancedDateTimeInterval => true
  | _ => false
  end.

Definition isNat {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | Nat₀ => true
  | _ => false
  end.

Definition isString {model : brand_model} (τ:rtype) :=
  match proj1_sig τ with
  | String₀ => true
  | _ => false
  end.

  Definition tuncoll {model:brand_model} (τ:rtype) : option rtype.
  Proof.
    destruct τ.
    destruct x.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact (Some (exist (fun τ₀ : rtype₀ => wf_rtype₀ τ₀ = true) x e)). 
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
  Defined.

Inductive date_time_unary_op_has_type {model:brand_model} :
  date_time_unary_op -> rtype -> rtype -> Prop
  :=
  | tuop_date_time_component part : date_time_unary_op_has_type (uop_date_time_component part) DateTime Nat
  | tuop_date_time_from_string : date_time_unary_op_has_type uop_date_time_from_string RType.String DateTime
  | tuop_date_time_duration_from_string : date_time_unary_op_has_type uop_date_time_duration_from_string RType.String DateTimeInterval
.

Definition date_time_unary_op_type_infer {model : brand_model} (op:date_time_unary_op) (τ₁:rtype) : option rtype :=
  match op with
  | uop_date_time_component part =>
    if isDateTime τ₁ then Some Nat else None
  | uop_date_time_from_string =>
    if isString τ₁ then Some DateTime else None
  | uop_date_time_duration_from_string =>
    if isString τ₁ then Some DateTimeInterval else None
  end.

Definition date_time_unary_op_type_infer_sub {model : brand_model} (op:date_time_unary_op) (τ₁:rtype) : option (rtype*rtype) :=
  match op with
  | uop_date_time_component part =>
    enforce_unary_op_schema (τ₁,DateTime) Nat
  | uop_date_time_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTime
  | uop_date_time_duration_from_string =>
    enforce_unary_op_schema (τ₁,RType.String) DateTimeInterval
  end.

Lemma date_time_unary_op_typing_sound {model : brand_model}
      (fu : date_time_unary_op) (τin τout : rtype) :
  date_time_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      date_time_unary_op_interp fu din = Some dout /\ dout ▹ τout.
Proof.
  inversion 1; subst;
    try solve[inversion 1; subst;
      try invcs H0;
      try invcs H3;
      simpl; unfold denhanceddateTime, denhanceddateTimeinterval; simpl;
      eexists; split; try reflexivity;
      repeat constructor].
Qed.

  Inductive enhanced_unary_op_has_type {model:brand_model} : enhanced_unary_op -> rtype -> rtype -> Prop
    :=
    | tenhanced_unary_date_time_op fu τin τout:
        date_time_unary_op_has_type fu τin τout ->
        enhanced_unary_op_has_type (enhanced_unary_date_time_op fu) τin τout.

  Definition enhanced_unary_op_typing_infer {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option rtype :=
    match fu with
    | enhanced_unary_date_time_op op => date_time_unary_op_type_infer op τ
    end.

  Lemma enhanced_unary_op_typing_infer_correct
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout} :
    enhanced_unary_op_typing_infer fu τ₁ = Some τout ->
    enhanced_unary_op_has_type fu τ₁ τout.
  Proof.
    intros.
    destruct fu; simpl.
    - destruct d; simpl in *.
      + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
        destruct ft; simpl in *; try congruence;
        inversion H; subst; clear H; constructor;
        rewrite Foreign_canon; constructor.
      + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence;
        inversion H; subst; clear H; constructor;
        rewrite String_canon; constructor.
      + destruct τ₁; simpl in *; try congruence;
        destruct x; simpl in *; try congruence.
        inversion H; subst; clear H; constructor.
        rewrite String_canon; constructor.
  Qed.

  Lemma enhanced_unary_op_typing_infer_least
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout₁ τout₂} :
    enhanced_unary_op_typing_infer fu τ₁ = Some τout₁ ->
    enhanced_unary_op_has_type fu τ₁ τout₂ ->
    τout₁ ≤ τout₂.
  Proof.
    intros.
    destruct fu; simpl in *.
    - destruct d; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence.
      + destruct ft; simpl in *; try congruence;
        inversion H; subst; clear H;
        rewrite Foreign_canon in H0;
        inversion H0; subst; clear H0;
        inversion H1; subst; clear H1;
        reflexivity.
      + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
        inversion H1; subst; clear H1;
        reflexivity.
      + inversion H; subst; clear H;
        rewrite String_canon in H0;
        inversion H0; subst; clear H0;
        inversion H1; subst; clear H1;
        reflexivity.
  Qed.

  Lemma enhanced_unary_op_typing_infer_complete
        {model:brand_model}
        (fu:foreign_unary_op_type)
        {τ₁ τout} : 
    enhanced_unary_op_typing_infer fu τ₁ = None ->
    ~ enhanced_unary_op_has_type fu τ₁ τout.
  Proof.
    intros.
    destruct fu; simpl in *.
    - destruct d; simpl in *;
      destruct τ₁; simpl in *; try congruence;
      destruct x; simpl in *; try congruence;
      unfold not; intros;
      inversion H0; subst; clear H0;
      inversion H2; subst; clear H2.
      + simpl in H; congruence.
  Qed.

  Definition enhanced_unary_op_typing_infer_sub {model:brand_model} (fu:enhanced_unary_op) (τ:rtype) : option (rtype*rtype) :=
    match fu with
    | enhanced_unary_date_time_op op => date_time_unary_op_type_infer_sub op τ
    end.
    
Lemma enhanced_unary_op_typing_sound {model : brand_model}
      (fu : foreign_unary_op_type) (τin τout : rtype) :
  enhanced_unary_op_has_type fu τin τout ->
  forall din : data,
    din ▹ τin ->
    exists dout : data,
      enhanced_unary_op_interp brand_relation_brands fu din = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply date_time_unary_op_typing_sound; eauto.
Qed.

Instance enhanced_foreign_unary_op_typing
        {model:brand_model} :
  @foreign_unary_op_typing
    enhanced_foreign_data
    enhanced_foreign_unary_op
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_unary_op_typing_has_type := enhanced_unary_op_has_type
       ; foreign_unary_op_typing_sound := enhanced_unary_op_typing_sound
       ; foreign_unary_op_typing_infer := enhanced_unary_op_typing_infer
       ; foreign_unary_op_typing_infer_correct := enhanced_unary_op_typing_infer_correct
       ; foreign_unary_op_typing_infer_least := enhanced_unary_op_typing_infer_least
       ; foreign_unary_op_typing_infer_complete := enhanced_unary_op_typing_infer_complete
       ; foreign_unary_op_typing_infer_sub := enhanced_unary_op_typing_infer_sub
     }.

Inductive date_time_binary_op_has_type {model:brand_model} :
  date_time_binary_op -> rtype -> rtype -> rtype -> Prop
  :=
  | tbop_date_time_plus :
      date_time_binary_op_has_type bop_date_time_plus DateTime DateTimeInterval DateTime 
  | tbop_date_time_minus :
      date_time_binary_op_has_type bop_date_time_minus DateTime DateTimeInterval DateTime 
  | tbop_date_time_ne :
      date_time_binary_op_has_type bop_date_time_ne DateTime DateTime Bool 
  | tbop_date_time_lt :
      date_time_binary_op_has_type bop_date_time_lt DateTime DateTime Bool 
  | tbop_date_time_le :
      date_time_binary_op_has_type bop_date_time_le DateTime DateTime Bool 
  | tbop_date_time_gt :
      date_time_binary_op_has_type bop_date_time_gt DateTime DateTime Bool 
  | tbop_date_time_ge :
      date_time_binary_op_has_type bop_date_time_ge DateTime DateTime Bool
  | tbop_date_time_duration  :
      date_time_binary_op_has_type bop_date_time_duration DateTime DateTime DateTimeInterval
  | tbop_date_time_duration_days  :
      date_time_binary_op_has_type bop_date_time_duration_days DateTime DateTime Float
  | tbop_date_time_duration_seconds  :
      date_time_binary_op_has_type bop_date_time_duration_seconds DateTime DateTime Float
.

Definition date_time_binary_op_type_infer {model : brand_model} (op:date_time_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | bop_date_time_plus =>
    if isDateTime τ₁ && isDateTimeInterval τ₂ then Some DateTime else None
  | bop_date_time_minus =>
    if isDateTime τ₁ && isDateTimeInterval τ₂ then Some DateTime else None
  | bop_date_time_ne =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_lt =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_le =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_gt =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_ge =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Bool else None
  | bop_date_time_duration  =>
    if isDateTime τ₁ && isDateTime τ₂ then Some DateTimeInterval else None
  | bop_date_time_duration_days  =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Float else None
  | bop_date_time_duration_seconds  =>
    if isDateTime τ₁ && isDateTime τ₂ then Some Float else None
  end.

Lemma date_time_binary_op_typing_sound {model : brand_model}
      (fb : date_time_binary_op) (τin₁ τin₂ τout : rtype) :
  date_time_binary_op_has_type fb τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      date_time_binary_op_interp fb din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
    inversion 1; subst;
      inversion 1; subst;
        inversion 1; subst;
      try invcs H0;
      try invcs H1;
      invcs H3;
      try invcs H4;
      simpl; 
        eexists; split; try reflexivity;
          repeat constructor.
Qed.
         
Definition date_time_binary_op_type_infer_sub {model : brand_model} (op:date_time_binary_op) (τ₁ τ₂:rtype) : option (rtype*rtype*rtype) :=
  match op with
  | bop_date_time_plus =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimeInterval) DateTime
  | bop_date_time_minus =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTimeInterval) DateTime
  | bop_date_time_ne
  | bop_date_time_lt
  | bop_date_time_le
  | bop_date_time_gt
  | bop_date_time_ge =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Bool
  | bop_date_time_duration  =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) DateTimeInterval
  | bop_date_time_duration_days  =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Float
  | bop_date_time_duration_seconds  =>
    enforce_binary_op_schema (τ₁,DateTime) (τ₂,DateTime) Float
  end.

Inductive enhanced_binary_op_has_type {model:brand_model} :
  enhanced_binary_op -> rtype -> rtype -> rtype -> Prop
    :=
    | tenhanced_binary_date_time_op fb τin₁ τin₂ τout:
        date_time_binary_op_has_type fb τin₁ τin₂ τout ->
        enhanced_binary_op_has_type (enhanced_binary_date_time_op fb) τin₁ τin₂ τout.

Definition enhanced_binary_op_typing_infer {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_date_time_op fb => date_time_binary_op_type_infer fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_infer_correct
      {model:brand_model}
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout} :
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  intros.
  destruct fb; simpl.
  - destruct d; simpl in *;
    destruct τ₁; destruct τ₂; simpl in *; try discriminate;
         unfold isDateTime, isDateTimeInterval, isNat in *
         ; destruct x; simpl in H; try discriminate
    ; destruct ft; simpl in H; try discriminate
    ; destruct x0; simpl in H; try discriminate
    ; try (destruct ft; simpl in H; try discriminate)
    ; invcs H
    ; constructor
    ; repeat rewrite Nat_canon
    ; repeat rewrite Foreign_canon
    ; try constructor.
Qed.

Lemma enhanced_binary_op_typing_infer_least
      {model:brand_model}
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout₁ τout₂} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = Some τout₁ ->
  enhanced_binary_op_has_type fb τ₁ τ₂ τout₂ ->
  τout₁ ≤ τout₂.
Proof.
  intros.
  destruct fb; simpl.
  - destruct d; simpl in *;
      destruct τ₁; destruct τ₂; simpl in *; try discriminate
    ; unfold isDateTime, isDateTimeInterval, isNat in *
    ; destruct x; simpl in H; try discriminate
    ; destruct ft; simpl in H; try discriminate
    ; destruct x0; simpl in H; try discriminate
    ; try (destruct ft; simpl in H; try discriminate)
    ; invcs H
    ; repeat rewrite Foreign_canon in H0
    ; invcs H0
    ; invcs H1
    ; reflexivity.
Qed.

Lemma enhanced_binary_op_typing_infer_complete
      {model:brand_model}
      (fb:foreign_binary_op_type)
      {τ₁ τ₂ τout} : 
  enhanced_binary_op_typing_infer fb τ₁ τ₂ = None ->
  ~ enhanced_binary_op_has_type fb τ₁ τ₂ τout.
Proof.
  destruct fb; simpl; intros.
  - intro HH; invcs HH.
    destruct d; simpl in *; invcs H1; simpl in H; try discriminate.
Qed.

Definition enhanced_binary_op_typing_infer_sub {model:brand_model} (op:enhanced_binary_op) (τ₁ τ₂:rtype) :=
  match op with
  | enhanced_binary_date_time_op fb => date_time_binary_op_type_infer_sub fb τ₁ τ₂
  end.

Lemma enhanced_binary_op_typing_sound {model : brand_model}
      (fu : foreign_binary_op_type) (τin₁ τin₂ τout : rtype) :
  enhanced_binary_op_has_type fu τin₁ τin₂ τout ->
  forall din₁ din₂ : data,
    din₁ ▹ τin₁ ->
    din₂ ▹ τin₂ ->
    exists dout : data,
      enhanced_binary_op_interp brand_relation_brands fu din₁ din₂ = Some dout /\ dout ▹ τout.
Proof.
  intros.
  destruct H.
  - eapply date_time_binary_op_typing_sound; eauto.
Qed.

Program Instance enhanced_foreign_binary_op_typing
        {model:brand_model} :
  @foreign_binary_op_typing
    enhanced_foreign_data
    enhanced_foreign_binary_op
    enhanced_foreign_type
    enhanced_foreign_data_typing
    model
  := { foreign_binary_op_typing_has_type := enhanced_binary_op_has_type
       ; foreign_binary_op_typing_sound := enhanced_binary_op_typing_sound
       ; foreign_binary_op_typing_infer := enhanced_binary_op_typing_infer
       ; foreign_binary_op_typing_infer_correct := enhanced_binary_op_typing_infer_correct
       ; foreign_binary_op_typing_infer_least := enhanced_binary_op_typing_infer_least
       ; foreign_binary_op_typing_infer_complete := enhanced_binary_op_typing_infer_complete
       ; foreign_binary_op_typing_infer_sub := enhanced_binary_op_typing_infer_sub
     }.

Instance enhanced_foreign_typing {model:brand_model}:
  @foreign_typing
    enhanced_foreign_runtime
    enhanced_foreign_type
    model
  := mk_foreign_typing
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_data_typing
       enhanced_foreign_unary_op_typing
       enhanced_foreign_binary_op_typing.

Instance enhanced_basic_model {model:brand_model} :
  basic_model
  := mk_basic_model
       enhanced_foreign_runtime
       enhanced_foreign_type
       model
       enhanced_foreign_typing.


Module EnhancedForeignType <: CompilerForeignType.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
End EnhancedForeignType.

Require Import ZArith.
Module EnhancedModel(bm:CompilerBrandModel(EnhancedForeignType)) <: CompilerModel.
  Definition compiler_foreign_type : foreign_type
    := enhanced_foreign_type.
  Definition compiler_basic_model : @basic_model
    := @enhanced_basic_model bm.compiler_brand_model.
  Definition compiler_model_foreign_to_java : foreign_to_java
    := enhanced_foreign_to_java.
  Definition compiler_model_foreign_to_javascript : foreign_to_javascript
    := enhanced_foreign_to_javascript.
  Definition compiler_model_foreign_to_ajavascript : foreign_to_ajavascript
    := enhanced_foreign_to_ajavascript.
  Definition compiler_model_foreign_to_scala : foreign_to_scala
    := enhanced_foreign_to_scala.
  Definition compiler_model_foreign_to_JSON : foreign_to_JSON
    := enhanced_foreign_to_JSON.
  Definition compiler_model_foreign_type_to_JSON : foreign_type_to_JSON
    := enhanced_foreign_type_to_JSON.
  Definition compiler_model_foreign_reduce_op : foreign_reduce_op
    := enhanced_foreign_reduce_op.
  Definition compiler_model_foreign_to_reduce_op : foreign_to_reduce_op
    := enhanced_foreign_to_reduce_op.
  Definition compiler_model_foreign_to_spark : foreign_to_spark
    := enhanced_foreign_to_spark.
  Definition compiler_model_foreign_cloudant : foreign_cloudant
    := enhanced_foreign_cloudant.
  Definition compiler_model_foreign_to_cloudant : foreign_to_cloudant
    := enhanced_foreign_to_cloudant.
  Definition compiler_model_nraenv_optimizer_logger : optimizer_logger string nraenv
    := foreign_nraenv_optimizer_logger.
  Definition compiler_model_nnrc_optimizer_logger : optimizer_logger string nnrc
    := foreign_nnrc_optimizer_logger.
  Definition compiler_model_nnrs_imp_expr_optimizer_logger : optimizer_logger string nnrs_imp_expr
    := foreign_nnrs_imp_expr_optimizer_logger.
  Definition compiler_model_nnrs_imp_stmt_optimizer_logger : optimizer_logger string nnrs_imp_stmt
    := foreign_nnrs_imp_stmt_optimizer_logger.
  Definition compiler_model_nnrs_imp_optimizer_logger : optimizer_logger string nnrs_imp
    := foreign_nnrs_imp_optimizer_logger.
  Definition compiler_model_dnnrc_optimizer_logger {br:brand_relation}: optimizer_logger string (@dnnrc_base _ (type_annotation unit) dataframe)
    := foreign_dnnrc_optimizer_logger.
  Definition compiler_model_foreign_data_typing : foreign_data_typing
    := enhanced_foreign_data_typing.
End EnhancedModel.

Module CompEnhanced.
  Module Enhanced.
  Module Model.
    Definition basic_model (bm:brand_model) : basic_model
      := @enhanced_basic_model bm.

    Definition foreign_type : foreign_type
      := enhanced_foreign_type.

    Definition foreign_typing (bm:brand_model) : foreign_typing
      := @enhanced_foreign_typing bm.

  End Model.

    Module Data.
      Definition dstringblob (s : STRING) : data
        := dforeign (enhancedstring s).
      Definition jstringblob (s : STRING) : json
        := jstring (jenhancedstring s).

      (* intended for generated coq code, to stand out and be more
          easily distinguished from variables (hackily distinguished
          that is) *)
      
      Definition date_time_part := date_time_component.
      Definition date_time_day : date_time_part := date_time_DAY.
      Definition date_time_month : date_time_part := date_time_MONTH.
      Definition date_time_quarter : date_time_part := date_time_QUARTER.
      Definition date_time_year : date_time_part := date_time_YEAR.

      Definition ddate_time (d:DATE_TIME) : data
        := dforeign (enhanceddateTime d).

      Definition ddate_time_duration (d:DATE_TIME_DURATION) : data
        := dforeign (enhanceddateTimeinterval d).

    End Data.

    Module Ops.
      Module Unary.
        Definition date_time_component (component:date_time_component)
          := OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component component)).
        Definition date_time_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_from_string).
        Definition date_time_duration_from_string
          := OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_string).

        (* for coq style syntax *)
        Definition OpDateTimeComponent := date_time_component.
        Definition OpDateTimeFromString := date_time_from_string.
        Definition OpDateTimeIntervalFromString := date_time_duration_from_string.
        
      End Unary.
      
      Module Binary.
        (* for ocaml *)
        Definition date_time_plus
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_plus).
        Definition date_time_minus
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_minus).
        Definition date_time_ne 
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_ne).
        Definition date_time_lt 
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_lt).
        Definition date_time_le 
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_le).
        Definition date_time_gt 
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_gt).
        Definition date_time_ge 
          := OpForeignBinary (enhanced_binary_date_time_op bop_date_time_ge).

        Definition date_time_duration_days
          := OpForeignBinary (enhanced_binary_date_time_op (bop_date_time_duration_days)).
        Definition date_time_duration_seconds 
          := OpForeignBinary (enhanced_binary_date_time_op (bop_date_time_duration_seconds)).
        
        (* for coq style syntax *)
        Definition OpDateTimePlus := date_time_plus.
        Definition OpDateTimeMinus := date_time_minus.
        Definition OpDateTimeNe := date_time_ne.
        Definition OpDateTimeLt := date_time_lt.
        Definition OpDateTimeLe := date_time_le.
        Definition OpDateTimeGt := date_time_gt.
        Definition OpDateTimeGe := date_time_ge.

        Definition OpDateTimeIntervalDays := date_time_duration_days.
        Definition OpDateTimeIntervalSeconds := date_time_duration_seconds.

      End Binary.
    End Ops.
  End Enhanced.
End CompEnhanced.  

