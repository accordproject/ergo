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

(** Translates ErgoNNRC to JavaScript *)

Require Import String.
Require Import List.

Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Driver.CompDriver.
Require Import ErgoSpec.Version.
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.ErgoImp.Lang.ErgoImp.
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.ErgoWasm.Lang.ErgoWasm.

Section ErgoImptoWasm.
  Local Open Scope list_scope.

  Context {bm:brand_model}.

  Axiom ergo_imp_ejson_to_wasm_ast : ergo_imp_module -> wasm_ast.

  Definition ergo_imp_module_to_wasm
             (contract_name:string)
             (p:ergo_imp_module) : wasm_ast :=
    ergo_imp_ejson_to_wasm_ast p.
End ErgoImptoWasm.

Extract Constant ergo_imp_ejson_to_wasm_ast => "Ergo_wasm_translate.ergo_imp".
