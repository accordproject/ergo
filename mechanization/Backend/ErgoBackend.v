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

Require Export Qcert.Utils.Utils.
Require Export Qcert.Common.TypingRuntime.

Require Qcert.Compiler.Model.EnhancedModel.
Require ErgoSpec.Backend.Model.ErgoBackendRuntime.
Require ErgoSpec.Backend.Lib.EType.
Require ErgoSpec.Backend.Lib.EData.
Require ErgoSpec.Backend.Lib.EOperators.
Require ErgoSpec.Backend.Lib.ECodeGen.

Module ErgoEnhancedBackend := ErgoBackendRuntime.ErgoBackendRuntime <+ EnhancedModel.CompEnhanced.
Module ErgoType := EType.EType(ErgoEnhancedBackend).
Module ErgoData := EData.EData(ErgoEnhancedBackend).
Module ErgoOps := EOperators.EOperators(ErgoEnhancedBackend).
Module ErgoCodeGen := ECodeGen.ECodeGen(ErgoEnhancedBackend).

