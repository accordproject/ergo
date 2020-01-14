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
Require Import Qcert.NNRCMR.Lang.ForeignReduceOps.
Require Import Qcert.Translation.Operators.ForeignToSpark.
(* NNRCMR rewrites *)
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Qcert.NNRCMR.NNRCMRRuntime.
Require Import Qcert.NNRCMR.Optim.NNRCMRRewrite.

Require Import QcertData.
Require Import QcertReduceOps.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nstring_scope.

Definition enhanced_to_spark_reduce_op
           (rop:enhanced_reduce_op)
           (scala_endl quotel:nstring) : nstring
  := match rop with
     | RedOpCount => ^".count().toString()"
     | RedOpSum enhanced_numeric_int => ^".aggregate(0)(_ + _.toInt, _ + _).toString()"
     | RedOpSum enhanced_numeric_float => ^".aggregate(0.0)(_ + _.toDouble, _ + _).toString()"
     | RedOpMin enhanced_numeric_int => ^".aggregate(Int.MaxValue)(((x, y) => Math.min(x, y.toInt)), Math.min).toString()"
     | RedOpMin enhanced_numeric_float => ^".aggregate(Double.MaxValue)(((x, y) => Math.min(x, y.toDouble)), Math.min).toString()"
     | RedOpMax enhanced_numeric_int =>
       ^".aggregate(Int.MinValue)(((x, y) => Math.max(x, y.toInt)), Math.max).toString()"
     | RedOpMax enhanced_numeric_float =>
       ^".aggregate(Double.MinValue)(((x, y) => Math.max(x, y.toDouble)), Math.max).toString()"
     | RedOpStats _ =>
       ^".aggregate("""")(statsReduce, statsRereduce).toString()" +++ scala_endl +++
                     ^"  sc.parallelize(Array(res))"
     | RedOpArithMean _ => (* assert false *)
       ^".arithmean /* ArithMean must be removed before code generation */"
     end.

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

