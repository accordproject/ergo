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
Require Import String.
Require Import List.
Require Import Qcert.Compiler.Model.EnhancedModel.
Require Import Qcert.Compiler.Model.SqlDateModelPart.
Require Import Qcert.cNNRC.Lang.cNNRC.

Module JuraRuntime <: JuraCompilerModel.
  Definition lookup_foreign_unary_operator (fname:string) (e:jurac_expr) : option jurac_expr :=
    None.

  Definition lookup_foreign_binary_operator (fname:string) (e1 e2:jurac_expr) : option jurac_expr :=
    let binop :=
        match fname with
        | "isAfter"%string =>
          Some (OpForeignBinary (enhanced_binary_sql_date_op
                                   bop_sql_date_gt))
        | "isBefore"%string =>
          Some (OpForeignBinary (enhanced_binary_sql_date_op
                                   bop_sql_date_lt))
        | _ => None
        end
    in
    match binop with
    | None => None
    | Some op => Some (NNRCBinop op e1 e2)
    end.

  Definition lookup_foreign_jura (fname:string) (el:list jurac_expr) : option jurac_expr :=
    match el with
    | e :: nil => lookup_foreign_unary_operator fname e
    | e1 :: e2 :: nil => lookup_foreign_binary_operator fname e1 e2
    | _ => None
    end.

  Definition jura_compiler_foreign_jura :=
    mk_foreign_jura _ lookup_foreign_jura.
End JuraRuntime.

