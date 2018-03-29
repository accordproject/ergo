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

Require Import Qcert.Common.CommonSystem.
Require Import Qcert.Compiler.Model.EnhancedModel.
Require Import Jura.Backend.ForeignJura.

Module Type JuraBackendModel.
  Definition jura_foreign_data : foreign_data := enhanced_foreign_data.
  Axiom jura_data_to_json_string : String.string -> data -> String.string.
  Axiom jura_backend_closure : Set.
  Axiom jura_backend_lookup_table : Set.
  Axiom jura_backend_foreign_jura : foreign_jura.
  Axiom jura_backend_stdlib : backend_lookup_table.
End JuraBackendModel.

