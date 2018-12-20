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
Require Import ErgoSpec.Backend.Model.MathModelPart.
Require Import ErgoSpec.Backend.Model.DateTimeModelPart.
Require Import ErgoSpec.Backend.Model.ErgoEnhancedModel.
Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCStdlib.
  Local Open Scope string.

  Definition empty_sigc prov (params:list string) :=
    mkSigC
      (List.map (fun x => (x,ErgoTypeAny prov)) params)
      (Some (ErgoTypeUnit prov)).

  Definition mk_naked_closure prov (params:list string) (body:ergoc_expr) : ergoc_function :=
    mkFuncC
      prov
      (empty_sigc prov params)
      (Some body).

  Definition mk_unary prov op : ergoc_function :=
    mk_naked_closure
      prov
      ("p0"::nil)
      (EUnaryOp prov op (EVar prov "p0")).

  Definition mk_binary_expr prov e : ergoc_function :=
    mk_naked_closure
      prov
      ("p1"::"p2"::nil)
      e.

  Definition mk_binary prov op : ergoc_function :=
    mk_binary_expr
      prov
      (EBinaryOp prov op (EVar prov "p1") (EVar prov "p2")).

  Definition mk_binary_rev prov op : ergoc_function :=
    mk_binary_expr
      prov
      (EBinaryOp prov op (EVar prov "p2") (EVar prov "p1")).

  Definition ergo_stdlib_table : Set := list (string * ergoc_function).
  
  Definition backend_compose_table (t1 t2:ergo_stdlib_table) : ergo_stdlib_table :=
    List.app t1 t2.

  Definition foreign_unary_operator_table prov : ergo_stdlib_table :=
    (* Math *)
    ("org.accordproject.ergo.stdlib.acos"%string,
     mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_acos)))
      :: ("org.accordproject.ergo.stdlib.asin",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_asin)))
      :: ("org.accordproject.ergo.stdlib.atan",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_atan)))
      :: ("org.accordproject.ergo.stdlib.cos",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_cos)))
      :: ("org.accordproject.ergo.stdlib.cosh",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_cosh)))
      :: ("org.accordproject.ergo.stdlib.sin",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_sin)))
      :: ("org.accordproject.ergo.stdlib.sinh",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_sinh)))
      :: ("org.accordproject.ergo.stdlib.tan",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_tan)))
      :: ("org.accordproject.ergo.stdlib.tanh",
          mk_unary prov (OpForeignUnary (enhanced_unary_math_op uop_math_tanh)))
    (* Date/Time *)
      :: ("org.accordproject.ergo.stdlib.dateTime"%string,
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op uop_date_time_from_string)))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetSecond",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_SECONDS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetMinute",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_MINUTES))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetHour",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_HOURS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetDay",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_DAYS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetWeek",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_WEEKS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetMonth",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_MONTHS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetQuarter",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_QUARTERS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeGetYear",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_component date_time_component_YEARS))))

      :: ("org.accordproject.ergo.stdlib.durationSeconds",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_SECONDS))))
      :: ("org.accordproject.ergo.stdlib.durationMinutes",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_MINUTES))))
      :: ("org.accordproject.ergo.stdlib.durationHours",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_HOURS))))
      :: ("org.accordproject.ergo.stdlib.durationDays",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_DAYS))))
      :: ("org.accordproject.ergo.stdlib.durationWeeks",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_WEEKS))))
      :: ("org.accordproject.ergo.stdlib.durationYears",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_duration_from_nat date_time_duration_YEARS))))

      :: ("org.accordproject.ergo.stdlib.durationAmount",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_amount)))

      :: ("org.accordproject.ergo.stdlib.periodDays",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_period_from_nat date_time_period_DAYS))))
      :: ("org.accordproject.ergo.stdlib.periodWeeks",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_period_from_nat date_time_period_WEEKS))))
      :: ("org.accordproject.ergo.stdlib.periodMonths",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_period_from_nat date_time_period_MONTHS))))
      :: ("org.accordproject.ergo.stdlib.periodQuarters",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_period_from_nat date_time_period_QUARTERS))))
      :: ("org.accordproject.ergo.stdlib.periodYears",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_period_from_nat date_time_period_YEARS))))

      :: ("org.accordproject.ergo.stdlib.dateTimeStartOfDay",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_DAYS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeStartOfWeek",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_WEEKS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeStartOfMonth",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_MONTHS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeStartOfQuarter",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_QUARTERS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeStartOfYear",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_YEARS))))

      :: ("org.accordproject.ergo.stdlib.dateTimeEndOfDay",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_DAYS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeEndOfWeek",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_WEEKS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeEndOfMonth",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_MONTHS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeEndOfQuarter",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_QUARTERS))))
      :: ("org.accordproject.ergo.stdlib.dateTimeEndOfYear",
          mk_unary prov (OpForeignUnary (enhanced_unary_date_time_op (uop_date_time_end_of date_time_period_YEARS))))
      :: nil.

  Definition foreign_binary_operator_table prov : ergo_stdlib_table :=
    (* Math *)
    ("org.accordproject.ergo.stdlib.atan2"%string,
     mk_binary prov (OpForeignBinary (enhanced_binary_math_op bop_math_atan2)))
    (* Date/Time *)
      :: ("org.accordproject.ergo.stdlib.dateTimeAddInternal",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_add)))
      :: ("org.accordproject.ergo.stdlib.dateTimeSubtractInternal",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_subtract)))
      :: ("org.accordproject.ergo.stdlib.dateTimeIsSame",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_same)))
      :: ("org.accordproject.ergo.stdlib.dateTimeIsBefore",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_before)))
      :: ("org.accordproject.ergo.stdlib.dateTimeIsAfter",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_is_after)))
      :: ("org.accordproject.ergo.stdlib.dateTimeDiffInternal",
          mk_binary prov (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_diff)))
      :: nil.

  Definition foreign_table prov : ergo_stdlib_table :=
    backend_compose_table (foreign_unary_operator_table prov)
                          (foreign_binary_operator_table prov).

  Definition unary_operator_table prov : ergo_stdlib_table :=
    ("org.accordproject.ergo.stdlib.toString", mk_unary prov OpToString)
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
      :: ("org.accordproject.ergo.stdlib.doubleToInteger", mk_unary prov OpFloatTruncate)
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
        :: ("org.accordproject.ergo.stdlib.arraySubtract", mk_binary_rev prov OpBagDiff)
        :: ("org.accordproject.ergo.stdlib.inArray", mk_binary prov OpContains)
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
