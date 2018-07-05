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

(** Compilation paths *)

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
Require Import ErgoSpec.Ergo.Lang.ErgoExpand.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import ErgoSpec.Translation.ErgotoErgoCalculus.
Require Import ErgoSpec.Translation.ErgoCalculustoErgoNNRC.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScriptCicero.
Require Import ErgoSpec.Translation.ErgoNNRCtoJava.

Section ErgoCompilerDriver.

  Definition compilation_ctxt : Set := list laergo_module * namespace_ctxt.
  Definition namespace_ctxt_of_compilation_ctxt (ctxt:compilation_ctxt) : namespace_ctxt :=
    snd ctxt.
  Definition modules_of_compilation_ctxt  (ctxt:compilation_ctxt) : list laergo_module :=
    fst ctxt.
  Definition update_namespace_ctxt (ctxt:compilation_ctxt) (ns_ctxt:namespace_ctxt) :=
    (fst ctxt, ns_ctxt).

  (* Initialize compilation context *)
  Definition compilation_ctxt_from_inputs
             (ctos:list lrcto_package)
             (mls:list lrergo_module) : eresult compilation_ctxt :=
    let ictos := map InputCTO ctos in
    let imls := map InputErgo mls in
    let ctxt := init_namespace_ctxt in
    resolve_ergo_inputs ctxt (ictos ++ imls).

  (* Ergo -> ErgoCalculus *)
  Definition ergo_module_to_ergo_calculus
             (ctxt:compilation_ctxt)
             (lm:lrergo_module) : eresult (ergoc_module * compilation_ctxt) :=
    let ns_ctxt := namespace_ctxt_of_compilation_ctxt ctxt in
    let am := resolve_ergo_module ns_ctxt lm in
    eolift (fun amc =>
              let ctxt := update_namespace_ctxt ctxt (snd amc) in
              let p := expand_ergo_module (fst amc) in
              elift (fun p => (ergo_module_to_calculus p, ctxt)) p) am.

  (* ErgoDecl -> ErgoCalculusDecl *)
  Definition ergo_declaration_to_ergo_calculus
             (ctxt:compilation_ctxt)
             (ld:lrergo_declaration) : eresult (option ergoc_declaration * compilation_ctxt) :=
    let ns_ctxt := namespace_ctxt_of_compilation_ctxt ctxt in
    let am := resolve_ergo_declaration ns_ctxt ld in
    elift (fun amc =>
             let ctxt := update_namespace_ctxt ctxt (snd amc) in
             (declaration_to_calculus (fst amc), ctxt)) am.

  Definition ergo_module_to_javascript
             (ctxt:compilation_ctxt)
             (p:lrergo_module) : eresult javascript :=
    let rmods := modules_of_compilation_ctxt ctxt in
    let pc := ergo_module_to_ergo_calculus ctxt p in
    let pn := eolift (fun xy => ergoc_module_to_nnrc rmods (fst xy)) pc in
    elift nnrc_module_to_javascript_top pn.

  Definition ergo_module_to_javascript_top
             (ctos:list lrcto_package)
             (mls:list lrergo_module)
             (p:lrergo_module) : eresult javascript :=
    let ctxt := compilation_ctxt_from_inputs ctos mls in
    eolift (fun ctxt => ergo_module_to_javascript ctxt p) ctxt.
  
  Definition ergo_module_to_java
             (ctxt:compilation_ctxt)
             (p:lrergo_module) : eresult java :=
    let rmods := modules_of_compilation_ctxt ctxt in
    let pc := ergo_module_to_ergo_calculus ctxt p in
    let pn := eolift (fun xy => ergoc_module_to_nnrc rmods (fst xy)) pc in
    elift nnrc_module_to_java_top pn.

  Definition ergo_module_to_java_top
             (ctos:list lrcto_package)
             (mls:list lrergo_module)
             (p:lrergo_module) : eresult java :=
    let ctxt := compilation_ctxt_from_inputs ctos mls in
    eolift (fun ctxt => ergo_module_to_java ctxt p) ctxt.

  Definition ergo_module_to_javascript_cicero_top
             (ctos:list cto_package)
             (mls:list lrergo_module)
             (p:ergo_module) : eresult javascript :=
    let ctxt := init_namespace_ctxt in
    let rctos := resolve_cto_packages ctxt ctos in
    let rmods := eolift (fun rctos => resolve_ergo_modules (snd rctos) mls) rctos in
    let p := eolift (fun pc => resolve_ergo_module (snd pc) p) rmods in
    let p := eolift (fun pc => expand_ergo_module (fst pc)) p in
    let ec := eolift lookup_single_contract p in
    eolift
      (fun c : ergo_contract =>
         let contract_name := c.(contract_name) in 
         let sigs := lookup_contract_signatures c in
         let pc := elift ergo_module_to_calculus p in
         let pn := eolift (fun rmods => eolift (ergoc_module_to_nnrc (fst rmods)) pc) rmods in
         elift (ergoc_module_to_javascript_cicero contract_name c.(contract_state) sigs) pn)
      ec.

End ErgoCompilerDriver.

