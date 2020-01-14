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
Require Import Qcert.Utils.Closure.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.NNRC.Lang.NNRC.

Section ForeignErgo.
  Context {fruntime:foreign_runtime}.

  Definition backend_closure : Set := @closure nnrc unit.
  Definition backend_lookup_table : Set := string -> option backend_closure.

  Class foreign_ergo : Type
    := mk_foreign_ergo {
           foreign_table : backend_lookup_table
         }.

End ForeignErgo.

