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

Require Import Qcert.Data.DataSystem.

Require Import ErgoSpec.Backend.Qcert.QcertModel.
Require Import ErgoSpec.Backend.ForeignErgo.

Module Type QBackendModel.
  Definition ergo_foreign_data : foreign_data := enhanced_foreign_data.
  Definition ergo_foreign_type : foreign_type := enhanced_foreign_type.
End QBackendModel.

