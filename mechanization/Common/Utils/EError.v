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

(* Built-in errors *)

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EResult.

Section EError.

  Definition dispatch_lookup_error {A} : eresult A :=
    efailure (CompilationError ("Cannot lookup created dispatch")).
  Definition dispatch_parameter_error {A} : eresult A :=
    efailure (CompilationError ("No parameter type in dispatch")).
  Definition not_in_contract_error {A} : eresult A :=
    efailure (CompilationError ("Cannot use 'contract' variable outside of a contract")).
  Definition not_in_clause_error {A} : eresult A :=
    efailure (CompilationError ("Cannot use 'clause' variable outside of a clause")).

  Definition ergo_default_package : string := "org.accordproject.ergo".
  Definition ergo_default_error_local_name : string := "Error".
  Definition ergo_default_error_name : string :=
    ergo_default_package ++ "." ++ ergo_default_error_local_name.

  Definition enforce_error_content : ErgoData.data :=
    ErgoData.dbrand (ergo_default_error_name::nil)
                    (ErgoData.drec (("message"%string, ErgoData.dstring "Enforce condition failed")::nil)).
  Definition enforce_error : eerror :=
    UserError enforce_error_content.

End EError.

