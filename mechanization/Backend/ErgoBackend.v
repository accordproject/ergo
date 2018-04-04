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

Require Qcert.Compiler.Model.EnhancedModel.
Require Ergo.Backend.Model.ErgoBackendRuntime.
Require Ergo.Backend.Lib.JType.
Require Ergo.Backend.Lib.JData.
Require Ergo.Backend.Lib.JOperators.
Require Ergo.Backend.Lib.JCodeGen.

Module ErgoEnhancedBackend := ErgoBackendRuntime.ErgoBackendRuntime <+ EnhancedModel.CompEnhanced.
Module ErgoType := JType.JType(ErgoEnhancedBackend).
Module ErgoData := JData.JData(ErgoEnhancedBackend).
Module ErgoOps := JOperators.JOperators(ErgoEnhancedBackend).
Module ErgoCodeGen := JCodeGen.JCodeGen(ErgoEnhancedBackend).

