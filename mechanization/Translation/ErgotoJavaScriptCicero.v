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

(** Translates contract logic to calculus *)

Require Import String.
Require Import List.
Require Import Qcert.Utils.ListAdd. (* For zip *)
Require Import Qcert.Compiler.Driver.CompLang.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoExpand.
Require Import ErgoSpec.Translation.ErgotoErgoCalculus.
Require Import ErgoSpec.Translation.ErgoCalculustoJavaScriptCicero.

Section ErgotoJavaScriptCicero.
  Definition ergo_package_to_javascript_cicero
             (ctos:list cto_package)
             (p:ergo_package) : eresult javascript :=
    let ec := lookup_single_contract p in
    let econame := elift (fun c => c.(contract_name)) ec in
    let p := ergo_package_expand p in
    let pc := eolift (package_to_calculus ctos) p in
    eolift (fun coname =>
              elift (ergoc_package_to_javascript_cicero coname) pc)
           econame.

End ErgotoJavaScriptCicero.

