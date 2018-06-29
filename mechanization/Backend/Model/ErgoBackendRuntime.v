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
Require Import Qcert.Utils.Closure.
Require Import Qcert.Common.CommonSystem.
Require Import Qcert.Compiler.Model.CompilerRuntime.
Require Import Qcert.Translation.NNRCtoJavaScript.
Require Import Qcert.cNNRC.Lang.cNNRC.

Require Import ErgoSpec.Backend.Model.DateTimeModelPart.
Require Import ErgoSpec.Backend.Model.ErgoEnhancedModel.
Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.

Definition mk_naked_closure (params:list string) (body:nnrc) : backend_closure :=
  let params := List.map (fun x => (x,None)) params in
  mkClosure
    params
    None
    body.

Definition backend_compose_table (t1 t2:backend_lookup_table) : backend_lookup_table :=
  fun fname =>
    match t1 fname with
    | None => t2 fname
    | Some cl => Some cl
    end.

Module ErgoBackendRuntime <: ErgoBackendModel.
  Local Open Scope string.

  Definition ergo_foreign_data := enhanced_foreign_data.
  Definition ergo_data_to_json_string := NNRCtoJavaScript.dataToJS.

  Definition ergo_backend_closure := backend_closure.
  Definition ergo_backend_lookup_table := backend_lookup_table.
  
  Definition foreign_unary_operator_table : ergo_backend_lookup_table :=
    fun fname =>
      let binop :=
          match fname with
          | "moment"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                    uop_date_time_from_string))
          | "momentDayOfMonth"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_DAY)))
          | "momentMonth"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_MONTH)))
          | "momentQuarter"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_QUARTER)))
          | "momentYear"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_YEAR))) 
         | _ => None
          end
      in
      match binop with
      | None => None
      | Some op =>
        Some (mk_naked_closure
                ("p1"::nil)
                (NNRCUnop op (NNRCGetConstant "p1")))
      end.



  Definition foreign_binary_operator_table : backend_lookup_table :=
    fun fname =>
      let binop :=
          match fname with
          | "momentIsAfter"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_gt))
          | "momentIsBefore"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_lt))
          | "momentSubtract"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_minus))
          | "momentAdd"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_plus))
          | "momentDiffDays"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_duration_days))
          | "momentDiffSeconds"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_duration_seconds))
          | _ => None
          end
      in
      match binop with
      | None => None
      | Some op =>
        Some (mk_naked_closure
                ("p1"::"p2"::nil)
                (NNRCBinop op (NNRCGetConstant "p1") (NNRCGetConstant "p2")))
      end.

  Definition foreign_function_table : backend_lookup_table :=
    fun fname =>
      match fname with
      | "momentIsSame"%string =>
        let e :=
            NNRCUnop
              OpNeg
              (NNRCBinop
                 (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_ne))
                 (NNRCGetConstant "p1") (NNRCGetConstant "p2"))
        in
        Some (mk_naked_closure
                ("p1"::"p2"::nil)
                e)
      | "momentDuration"%string =>
        let e :=
            NNRCLet "v1"%string (NNRCUnop OpToString (NNRCGetConstant "p1"%string))
                    (NNRCLet "v2"%string
                             (NNRCBinop OpStringConcat
                                        (NNRCConst (dstring "-"%string))
                                        (NNRCGetConstant "p2"%string))
                             (NNRCUnop
                                (OpForeignUnary (enhanced_unary_date_time_op uop_date_time_duration_from_string))
                                (NNRCBinop OpStringConcat
                                           (NNRCVar "v1"%string)
                                           (NNRCVar "v2"%string))))
        in 
        Some (mk_naked_closure
                ("p1"::"p2"::nil)
                e)
      | _ => None
      end.

  Definition foreign_table : backend_lookup_table :=
    backend_compose_table foreign_function_table
                          (backend_compose_table foreign_unary_operator_table
                                                 foreign_binary_operator_table).

  Definition ergo_backend_foreign_ergo :=
    mk_foreign_ergo foreign_table.

  Definition unary_operator_table : backend_lookup_table :=
    fun fname =>
      let unop :=
          match fname with
          (* Polymorphic *)
          | "toString" => Some OpToString
          (* Data *)
          | "some" => Some OpLeft
          (* Natural numbers // Integer or Long *)
          | "integerAbs" => Some (OpNatUnary NatAbs)
          | "integerlog2" => Some (OpNatUnary NatLog2)
          | "integerSqrt" => Some (OpNatUnary NatSqrt)
          | "integerToDouble" => Some OpFloatOfNat
          (* Floating point numbers // Double *)
          | "sqrt" => Some (OpFloatUnary FloatSqrt)
          | "exp" => Some (OpFloatUnary FloatExp)
          | "log" => Some (OpFloatUnary FloatLog)
          | "log10" => Some (OpFloatUnary FloatLog10)
          | "ceil" => Some (OpFloatUnary FloatCeil)
          | "floor" => Some (OpFloatUnary FloatFloor)
          | "abs" => Some (OpFloatUnary FloatAbs)
          | "max" => Some OpFloatBagMax
          | "min" => Some OpFloatBagMin
          | "average" => Some OpFloatMean
          | "sum" => Some OpFloatSum
          | "doubletoInteger" | "truncate" => Some OpFloatTruncate
          (* Arrays *)
          | "distinct" => Some OpDistinct
          | "count" => Some OpCount
          | "flatten" => Some OpFlatten
          | _ => None
          end
      in
      match unop with
      | None => None
      | Some op =>
        Some (mk_naked_closure
                ("p1"::nil)
                (NNRCUnop op (NNRCGetConstant "p1")))
      end.

    Definition binary_operator_table : backend_lookup_table :=
      fun fname =>
        let binop :=
            match fname with
            (* Natural numbers // Integer or Long *)
            | "integerMod" => Some (OpNatBinary NatRem)
            | "integerMin" => Some (OpNatBinary NatMin)
            | "integerMax" => Some (OpNatBinary NatMax)
            (* Floating point numbers // Double *)
            | "min" => Some (OpFloatBinary FloatMin)
            | "max" => Some (OpFloatBinary FloatMax)
            (* Arrays *)
            | "arrayAdd" => Some OpBagUnion
            | "arraySubstract" => Some OpBagDiff
            | _ => None
            end
        in
        match binop with
        | None => None
        | Some op =>
          Some (mk_naked_closure
                  ("p1"::"p2"::nil)
                  (NNRCBinop op (NNRCGetConstant "p1") (NNRCGetConstant "p2")))
        end.

    Definition builtin_table : backend_lookup_table :=
      fun fname =>
        match fname with
        | "now" =>
          Some (mk_naked_closure
                  nil
                  (NNRCGetConstant "now"))
        | _ => None
        end.

    Definition ergo_backend_stdlib : backend_lookup_table :=
      backend_compose_table foreign_table
     (backend_compose_table builtin_table
     (backend_compose_table unary_operator_table binary_operator_table)).

End ErgoBackendRuntime.
