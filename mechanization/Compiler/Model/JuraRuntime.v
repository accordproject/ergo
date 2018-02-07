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

Require Import Qcert.Common.CommonSystem.
Require Import Qcert.Compiler.Model.CompilerRuntime.
Require Import Qcert.Compiler.Model.DateTimeModelPart.
Require Import ForeignJura.
Require Import JuraModel.
Require Import JuraCalculus.
Require Import JuraCalculusCall.
Require Import String.
Require Import List.
Require Import Qcert.Compiler.Model.EnhancedModel.
Require Import Qcert.Compiler.Model.SqlDateModelPart.
Require Import Qcert.cNNRC.Lang.cNNRC.

Module JuraRuntime <: JuraCompilerModel.
  Local Open Scope string.
  Definition foreign_unary_operator_table : lookup_table :=
    fun fname => None.
            
  Definition foreign_binary_operator_table : lookup_table :=
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
        Some (@mkClosure _
                         ("p1"::"p2"::nil)
                         (NNRCBinop op (NNRCVar "p1") (NNRCVar "p2")))
      end.

  Definition foreign_function_table : lookup_table :=
    fun fname =>
      match fname with
      | "momentDuration"%string =>
        let e :=
            NNRCLet "v1"%string (NNRCUnop OpToString (NNRCVar "p1"%string))
                    (NNRCLet "v2"%string
                             (NNRCBinop OpStringConcat
                                        (NNRCConst (dstring "-"%string))
                                        (NNRCVar "p2"%string))
                             (NNRCUnop
                                (OpForeignUnary (enhanced_unary_sql_date_op uop_sql_date_interval_from_string))
                                (NNRCBinop OpStringConcat
                                           (NNRCVar "v1"%string)
                                           (NNRCVar "v2"%string))))
        in 
        Some (@mkClosure _
                         ("p1"::"p2"::nil)
                         e)
      | _ => None
      end.

  Definition foreign_table : lookup_table :=
    compose_table foreign_function_table
                  (compose_table foreign_unary_operator_table
                                 foreign_binary_operator_table).

  Definition jura_compiler_foreign_jura :=
    mk_foreign_jura _ foreign_table.
End JuraRuntime.

