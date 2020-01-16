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
Require Export ForeignModel.

Require ErgoSpec.Backend.Qcert.QcertModel.
Require ErgoSpec.Backend.Lib.QBackendRuntime.
Require ErgoSpec.Backend.Lib.QType.
Require ErgoSpec.Backend.Lib.QData.
Require ErgoSpec.Backend.Lib.QOps.
Require ErgoSpec.Backend.Lib.QCodeGen.

Module QcertBackend := QBackendRuntime.QBackendRuntime <+ QcertModel.CompEnhanced.
Module QcertData := QData.QData(QcertBackend).
Module QcertOps := QOps.QOps(QcertBackend).
Module QcertCodeGen := QCodeGen.QCodeGen(QcertBackend).
Module QcertType := QType.QType(QcertBackend).

(* Useful definitions *)
Section Defs.
  Definition zip {A} {B} : list A -> list B -> option (list (A * B)) := zip.
  Definition ergo_data := QcertData.data.
  Definition ergoc_type {br} := @QcertType.ectype br.
End Defs.

