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
Require Import Qcert.Common.ForeignRuntime.
Require Import Qcert.Common.CommonRuntime.
Require Import Qcert.Translation.ForeignToJava.
Require Import Qcert.Translation.ForeignToJavaScript.
Require Import Qcert.Translation.ForeignToScala.
Require Import Qcert.Common.Data.ForeignDataToJSON.
Require Import Qcert.Common.TypeSystem.ForeignTypeToJSON.
Require Import Qcert.NNRCMR.Lang.ForeignReduceOps.
Require Import Qcert.Translation.ForeignToReduceOps.
Require Import Qcert.Translation.ForeignToSpark.
Require Import Qcert.CldMR.Lang.ForeignCloudant.
Require Import Qcert.Translation.ForeignToCloudant.
Require Import Qcert.Utils.OptimizerLogger.
Require Import Qcert.Common.TypeSystem.ForeignType.
Require Import Qcert.Common.DataTyping.ForeignDataTyping.
Require Import Qcert.cNNRC.Lang.cNNRC.
Require Import Qcert.cNRAEnv.Lang.cNRAEnv.
Require Import Qcert.NRAEnv.Lang.NRAEnv.
Require Import Qcert.DNNRC.Lang.DNNRC.
Require Import Qcert.tDNNRC.Lang.tDNNRC.
Require Import ForeignJura.
Require Import Qcert.Compiler.Model.EnhancedModel.

Module Type JuraCompilerModel.
  Axiom jura_compiler_foreign_jura : foreign_jura.
End JuraCompilerModel.

