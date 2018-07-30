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

Require Import Qcert.Common.CommonSystem.
Require Import ErgoSpec.Backend.Model.DateTimeModelPart.
Require Import ErgoSpec.Backend.Model.ErgoEnhancedModel.
Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.

Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCStdlib.
  Local Open Scope string.

  Definition empty_sigc prov (params:list string) :=
    mkSigC
      (List.map (fun x => (x,ErgoTypeAny prov)) params)
      (ErgoTypeNone prov).
  
  Definition mk_naked_closure prov (params:list string) (body:ergoc_expr) : ergoc_function :=
    mkFuncC
      prov
      (empty_sigc prov params)
      (Some body).

  Definition mk_unary prov op : ergoc_function :=
    mk_naked_closure
      prov
      ("p1"::nil)
      (EUnaryOp prov op (EVar prov "p1")).

  Definition mk_binary_expr prov e : ergoc_function :=
    mk_naked_closure
      prov
      ("p1"::"p2"::nil)
      e.

  Definition mk_binary prov op : ergoc_function :=
    mk_binary_expr
      prov
      (EBinaryOp prov op (EVar prov "p1") (EVar prov "p2")).

  Definition ergo_stdlib_table : Set := list (string * ergoc_function).
  
  Definition backend_compose_table (t1 t2:ergo_stdlib_table) : ergo_stdlib_table :=
    List.app t1 t2.

  Definition foreign_unary_operator_table prov : ergo_stdlib_table :=
    ("org.accordproject.ergo.stdlib.moment"%string,
     mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op uop_date_time_from_string)))
      :: ("org.accordproject.ergo.stdlib.momentDayOfMonth",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_DAY))))
      :: ("org.accordproject.ergo.stdlib.momentMonth",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_MONTH))))
      :: ("org.accordproject.ergo.stdlib.momentQuarter",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_QUARTER))))
      :: ("org.accordproject.ergo.stdlib.momentYear",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_YEAR))))
      :: nil.

  Definition foreign_binary_operator_table prov : ergo_stdlib_table :=
    ("org.accordproject.ergo.stdlib.momentIsAfter",
     mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_gt)))
  :: ("org.accordproject.ergo.stdlib.momentIsBefore",
      mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_lt)))
  :: ("org.accordproject.ergo.stdlib.momentSubtract",
      mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_minus)))
  :: ("org.accordproject.ergo.stdlib.momentAdd",
      mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_plus)))
  :: ("org.accordproject.ergo.stdlib.momentDiffDays",
      mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_duration_days)))
  :: ("org.accordproject.ergo.stdlib.momentDiffSeconds",
      mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_duration_seconds)))
  :: nil.

  Definition foreign_function_table prov : ergo_stdlib_table :=
    ("org.accordproject.ergo.stdlib.momentIsSame",
     mk_binary_expr
       prov
       (EUnaryOp
          prov
          OpNeg
          (EBinaryOp
             prov
             (OpForeignBinary (enhanced_binary_date_time_op
                                 bop_date_time_ne))
             (EVar prov "p1") (EVar prov "p2"))))
      :: ("org.accordproject.ergo.stdlib.momentDuration",
          mk_binary_expr
            prov
            (ELet prov
                  "v1"%string
                  None
                  (EUnaryOp prov OpToString (EVar prov "p1"%string))
                  (ELet prov "v2"%string None
                        (EBinaryOp prov OpStringConcat
                                   (EConst prov (dstring "-"%string))
                                   (EVar prov "p2"%string))
                        (EUnaryOp prov
                                  (OpForeignUnary
                                     (enhanced_unary_date_time_op uop_date_time_duration_from_string))
                                  (EBinaryOp prov OpStringConcat
                                             (EVar prov "v1"%string)
                                             (EVar prov "v2"%string))))))
      :: nil.

  Definition foreign_table prov : ergo_stdlib_table :=
    backend_compose_table (foreign_function_table prov)
                          (backend_compose_table (foreign_unary_operator_table prov)
                                                 (foreign_binary_operator_table prov)).

  Definition unary_operator_table prov : ergo_stdlib_table :=
    ("org.accordproject.ergo.stdlib.toString", mk_unary prov OpToString)
      (* Data *)
      :: ("org.accordproject.ergo.stdlib.some", mk_unary prov OpLeft)
      (* Natural numbers // Integer or Long *)
      :: ("org.accordproject.ergo.stdlib.integerAbs", mk_unary prov (OpNatUnary NatAbs))
      :: ("org.accordproject.ergo.stdlib.integerLog2", mk_unary prov (OpNatUnary NatLog2))
      :: ("org.accordproject.ergo.stdlib.integerSqrt", mk_unary prov (OpNatUnary NatSqrt))
      :: ("org.accordproject.ergo.stdlib.integerToDouble", mk_unary prov OpFloatOfNat)
      (* Floating point numbers // Double *)
      :: ("org.accordproject.ergo.stdlib.sqrt", mk_unary prov (OpFloatUnary FloatSqrt))
      :: ("org.accordproject.ergo.stdlib.exp", mk_unary prov (OpFloatUnary FloatExp))
      :: ("org.accordproject.ergo.stdlib.log", mk_unary prov (OpFloatUnary FloatLog))
      :: ("org.accordproject.ergo.stdlib.log10", mk_unary prov (OpFloatUnary FloatLog10))
      :: ("org.accordproject.ergo.stdlib.ceil", mk_unary prov (OpFloatUnary FloatCeil))
      :: ("org.accordproject.ergo.stdlib.floor", mk_unary prov (OpFloatUnary FloatFloor))
      :: ("org.accordproject.ergo.stdlib.abs", mk_unary prov (OpFloatUnary FloatAbs))
      :: ("org.accordproject.ergo.stdlib.max", mk_unary prov OpFloatBagMax)
      :: ("org.accordproject.ergo.stdlib.min", mk_unary prov OpFloatBagMin)
      :: ("org.accordproject.ergo.stdlib.average", mk_unary prov OpFloatMean)
      :: ("org.accordproject.ergo.stdlib.sum", mk_unary prov OpFloatSum)
      :: ("org.accordproject.ergo.stdlib.doubletoInteger", mk_unary prov OpFloatTruncate)
      :: ("org.accordproject.ergo.stdlib.truncate", mk_unary prov OpFloatTruncate)
      (* Arrays *)
      :: ("org.accordproject.ergo.stdlib.distinct", mk_unary prov OpDistinct)
      :: ("org.accordproject.ergo.stdlib.count", mk_unary prov OpCount)
      :: ("org.accordproject.ergo.stdlib.flatten", mk_unary prov OpFlatten)
      :: nil.

    Definition binary_operator_table prov : ergo_stdlib_table :=
      (* Natural numbers // Integer or Long *)
      ("org.accordproject.ergo.stdlib.integerMod", mk_binary prov (OpNatBinary NatRem))
        :: ("org.accordproject.ergo.stdlib.integerMin", mk_binary prov (OpNatBinary NatMin))
        :: ("org.accordproject.ergo.stdlib.integerMax", mk_binary prov (OpNatBinary NatMax))
        (* Floating point numbers // Double *)
        :: ("org.accordproject.ergo.stdlib.minPair", mk_binary prov (OpFloatBinary FloatMin))
        :: ("org.accordproject.ergo.stdlib.maxPair", mk_binary prov (OpFloatBinary FloatMax))
        (* Arrays *)
        :: ("org.accordproject.ergo.stdlib.arrayAdd", mk_binary prov OpBagUnion)
        :: ("org.accordproject.ergo.stdlib.arraySubstract", mk_binary prov OpBagDiff)
        :: nil.

    Definition builtin_table prov : ergo_stdlib_table :=
      ("org.accordproject.ergo.stdlib.now", mk_naked_closure prov nil (EVar prov "now"))
        :: nil.

    Definition ergoc_stdlib : ergo_stdlib_table :=
      let prov := dummy_provenance in
      backend_compose_table (foreign_table prov)
     (backend_compose_table (builtin_table prov)
     (backend_compose_table (unary_operator_table prov) (binary_operator_table prov))).

End ErgoCStdlib.
