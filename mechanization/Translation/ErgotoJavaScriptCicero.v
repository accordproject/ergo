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
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoNameResolve.
Require Import ErgoSpec.Ergo.Lang.ErgoExpand.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgotoErgoCalculus.
Require Import ErgoSpec.Translation.ErgoCalculustoErgoNNRC.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScriptCicero.

Section ErgotoJavaScriptCicero.
  Definition ergo_module_to_javascript_cicero
             (ctos:list cto_package)
             (ml:list lrergo_module)
             (p:ergo_module) : eresult javascript :=
    let mctos := map cto_package_to_ergo_module ctos in
    let nsctxt := namespace_ctxt_of_ergo_modules (mctos ++ ml ++ (p::nil)) in
    let rctos := resolve_ergo_all_modules nsctxt mctos in
    let p := resolve_ergo_single_module nsctxt p in
    let p := eolift expand_ergo_module p in
    let ec := eolift lookup_single_contract p in
    eolift
      (fun c : ergo_contract =>
         let contract_name := c.(contract_name) in 
         let sigs := lookup_contract_signatures c in
         let pc := elift ergo_module_to_calculus p in
         let pn := eolift (fun rctos => eolift (ergoc_module_to_nnrc rctos) pc) rctos in
         elift (ergoc_module_to_javascript_cicero contract_name c.(contract_state) sigs) pn)
      ec.

End ErgotoJavaScriptCicero.

