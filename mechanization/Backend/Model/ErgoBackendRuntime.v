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
Require Import Qcert.Compiler.Model.DateTimeModelPart.
Require Import Qcert.Compiler.Model.EnhancedModel.
Require Import Qcert.Compiler.Model.SqlDateModelPart.
Require Import Qcert.Translation.NNRCtoJavaScript.
Require Import Qcert.cNNRC.Lang.cNNRC.
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
    fun fname => None.

  Definition foreign_binary_operator_table : backend_lookup_table :=
    fun fname =>
      let binop :=
          match fname with
          | "momentIsAfter"%string =>
            Some (OpForeignBinary (enhanced_binary_sql_date_op
                                     bop_sql_date_gt))
          | "momentIsBefore"%string =>
            Some (OpForeignBinary (enhanced_binary_sql_date_op
                                     bop_sql_date_lt))
          | "momentSubtract"%string =>
            Some (OpForeignBinary (enhanced_binary_sql_date_op
                                     bop_sql_date_minus))
          | "momentAdd"%string =>
            Some (OpForeignBinary (enhanced_binary_sql_date_op
                                     bop_sql_date_plus))
          | "momentDiff"%string =>
            Some (OpForeignBinary (enhanced_binary_sql_date_op
                                     bop_sql_date_interval_between))
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
      | "momentDuration"%string =>
        let e :=
            NNRCLet "v1"%string (NNRCUnop OpToString (NNRCGetConstant "p1"%string))
                    (NNRCLet "v2"%string
                             (NNRCBinop OpStringConcat
                                        (NNRCConst (dstring "-"%string))
                                        (NNRCGetConstant "p2"%string))
                             (NNRCUnop
                                (OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_interval_from_string))
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
          | "max" => Some OpFloatBagMax
          | "min" => Some OpFloatBagMin
          | "flatten" => Some OpFlatten
          | "toString" => Some OpToString
          | "count" => Some OpCount
          | "average" => Some OpFloatMean
          | "sum" => Some OpFloatSum
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
            | "concat" => Some OpStringConcat
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
