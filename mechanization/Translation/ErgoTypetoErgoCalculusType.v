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

(* Support for ErgoType models *)

Require Import String.
Require Import List.
Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.TypingRuntime.

Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EImport.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoTypetoErgoCalculusType.

  (** A semantics for ErgoCalculusType packages is obtained through translation
      into branded types. *)
  Program Fixpoint ergo_type_to_ergoc_type {m:brand_relation} (t:ergo_type) : ErgoCalculusType.ectype :=
    match type_desc t with
    | ErgoTypeAny => ErgoCalculusType.top
    | ErgoTypeNone => ErgoCalculusType.empty
    | ErgoTypeBoolean => ErgoCalculusType.bool
    | ErgoTypeString => ErgoCalculusType.string
    | ErgoTypeDouble => ErgoCalculusType.double
    | ErgoTypeLong => ErgoCalculusType.integer (* XXX To be decided *)
    | ErgoTypeInteger => ErgoCalculusType.integer
    | ErgoTypeDateTime => ErgoCalculusType.empty (* XXX TBD *)
    | ErgoTypeClassRef cr =>
      ErgoCalculusType.brand (absolute_name_of_name_ref "UNKNOWN.NAMESPACE"%string cr::nil)
    | ErgoTypeOption t =>
      ErgoCalculusType.option (ergo_type_to_ergoc_type t)
    | ErgoTypeRecord rtl =>
      ErgoCalculusType.record
        ErgoCalculusType.open_kind
        (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
        (rec_sort_sorted
           (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl)
           (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
           eq_refl)
    | ErgoTypeArray t => ErgoCalculusType.array (ergo_type_to_ergoc_type t)
    | ErgoTypeSum t1 t2 => ErgoCalculusType.sum (ergo_type_to_ergoc_type t1) (ergo_type_to_ergoc_type t2)
    end.

End ErgoTypetoErgoCalculusType.
