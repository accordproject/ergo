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
          | "org.accordproject.ergo.stdlib.moment"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                    uop_date_time_from_string))
          | "org.accordproject.ergo.stdlib.momentDayOfMonth"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_DAY)))
          | "org.accordproject.ergo.stdlib.momentMonth"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_MONTH)))
          | "org.accordproject.ergo.stdlib.momentQuarter"%string =>
            Some (OpForeignUnary (enhanced_unary_date_time_op
                                     (uop_date_time_component date_time_QUARTER)))
          | "org.accordproject.ergo.stdlib.momentYear"%string =>
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
          | "org.accordproject.ergo.stdlib.momentIsAfter"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_gt))
          | "org.accordproject.ergo.stdlib.momentIsBefore"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_lt))
          | "org.accordproject.ergo.stdlib.momentSubtract"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_minus))
          | "org.accordproject.ergo.stdlib.momentAdd"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_plus))
          | "org.accordproject.ergo.stdlib.momentDiffDays"%string =>
            Some (OpForeignBinary (enhanced_binary_date_time_op
                                     bop_date_time_duration_days))
          | "org.accordproject.ergo.stdlib.momentDiffSeconds"%string =>
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
      | "org.accordproject.ergo.stdlib.momentIsSame"%string =>
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
      | "org.accordproject.ergo.stdlib.momentDuration"%string =>
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
          | "org.accordproject.ergo.stdlib.toString" => Some OpToString
          (* Data *)
          | "org.accordproject.ergo.stdlib.some" => Some OpLeft
          (* Natural numbers // Integer or Long *)
          | "org.accordproject.ergo.stdlib.integerAbs" => Some (OpNatUnary NatAbs)
          | "org.accordproject.ergo.stdlib.integerlog2" => Some (OpNatUnary NatLog2)
          | "org.accordproject.ergo.stdlib.integerSqrt" => Some (OpNatUnary NatSqrt)
          | "org.accordproject.ergo.stdlib.integerToDouble" => Some OpFloatOfNat
          (* Floating point numbers // Double *)
          | "org.accordproject.ergo.stdlib.sqrt" => Some (OpFloatUnary FloatSqrt)
          | "org.accordproject.ergo.stdlib.exp" => Some (OpFloatUnary FloatExp)
          | "org.accordproject.ergo.stdlib.log" => Some (OpFloatUnary FloatLog)
          | "org.accordproject.ergo.stdlib.log10" => Some (OpFloatUnary FloatLog10)
          | "org.accordproject.ergo.stdlib.ceil" => Some (OpFloatUnary FloatCeil)
          | "org.accordproject.ergo.stdlib.floor" => Some (OpFloatUnary FloatFloor)
          | "org.accordproject.ergo.stdlib.abs" => Some (OpFloatUnary FloatAbs)
          | "org.accordproject.ergo.stdlib.max" => Some OpFloatBagMax
          | "org.accordproject.ergo.stdlib.min" => Some OpFloatBagMin
          | "org.accordproject.ergo.stdlib.average" => Some OpFloatMean
          | "org.accordproject.ergo.stdlib.sum" => Some OpFloatSum
          | "org.accordproject.ergo.stdlib.doubletoInteger" | "org.accordproject.ergo.stdlib.truncate" => Some OpFloatTruncate
          (* Arrays *)
          | "org.accordproject.ergo.stdlib.distinct" => Some OpDistinct
          | "org.accordproject.ergo.stdlib.count" => Some OpCount
          | "org.accordproject.ergo.stdlib.flatten" => Some OpFlatten
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
            | "org.accordproject.ergo.stdlib.integerMod" => Some (OpNatBinary NatRem)
            | "org.accordproject.ergo.stdlib.integerMin" => Some (OpNatBinary NatMin)
            | "org.accordproject.ergo.stdlib.integerMax" => Some (OpNatBinary NatMax)
            (* Floating point numbers // Double *)
            | "org.accordproject.ergo.stdlib.min" => Some (OpFloatBinary FloatMin)
            | "org.accordproject.ergo.stdlib.max" => Some (OpFloatBinary FloatMax)
            (* Arrays *)
            | "org.accordproject.ergo.stdlib.arrayAdd" => Some OpBagUnion
            | "org.accordproject.ergo.stdlib.arraySubstract" => Some OpBagDiff
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
        | "org.accordproject.ergo.stdlib.now" =>
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
