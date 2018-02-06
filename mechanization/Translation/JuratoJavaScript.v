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
Require Import Qcert.Common.CommonSystem.
Require Import Qcert.Utils.OptimizerLogger.
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Qcert.Compiler.Driver.CompLang.
Require Import Error.
Require Import ForeignJura.
Require Import Jura.
Require Import JuratoJuraCalculus.
Require Import JuraCalculustoJavaScript.

Section JuratoJavaScript.
  Context {fruntime:foreign_runtime}.
  Context {fjura:foreign_jura}.

  Definition clause_calculus_from_package
             (coname:string) (clname:string) (p:jura_package) : jresult nnrc :=
    let pc := package_to_calculus p in
    jolift (lookup_clause_code_from_package coname clname) pc.

  (* Basic modules *)
  (* Foreign Datatypes Support *)
  Require Import Qcert.Translation.ForeignToJavaScript.

  (* Context *)
  Context {ft:foreign_type}.
  Context {bm:brand_model}.
  Context {ftyping: foreign_typing}.
  Context {nnrc_logger:optimizer_logger string nnrc}.
  Context {ftojs:foreign_to_javascript}.
  Context {ftjson:foreign_to_JSON}.

  Definition clause_code_from_package (coname:string) (clname:string) (p:jura_package) : jresult javascript :=
    let pc := package_to_calculus p in
    jolift (javascript_of_clause_code_in_package coname clname) pc.
  
  Definition javascript_from_package (p:jura_package) : jresult javascript :=
    let pc := package_to_calculus p in
    jlift javascript_of_package_top pc.

End JuratoJavaScript.

