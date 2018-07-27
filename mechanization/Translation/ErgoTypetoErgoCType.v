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

Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoTypetoErgoCType.
  Context {m:brand_relation}.
  Import ErgoCTypes.

  Fixpoint ergo_type_to_ergoc_type (t:laergo_type) : ergoc_type :=
    match t with
    | ErgoTypeAny _ => ttop
    | ErgoTypeNone _ => tbottom
    | ErgoTypeBoolean _ => tbool
    | ErgoTypeString _ => tstring
    | ErgoTypeDouble _ => tfloat
    | ErgoTypeLong _ => tfloat
    | ErgoTypeInteger _ => tnat
    | ErgoTypeDateTime _ => tbottom
    | ErgoTypeClassRef _ cr => tbrand (cr::nil)
    | ErgoTypeOption _ t => teither (ergo_type_to_ergoc_type t) tunit
    | ErgoTypeRecord _ rtl =>
      trec
        open_kind
        (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
        (rec_sort_sorted
           (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl)
           (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
           eq_refl)
    | ErgoTypeArray _ t => tcoll (ergo_type_to_ergoc_type t)
    | ErgoTypeSum _ t1 t2 => teither (ergo_type_to_ergoc_type t1) (ergo_type_to_ergoc_type t2)
    end.

End ErgoTypetoErgoCType.