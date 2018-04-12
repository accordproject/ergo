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

(* Support for CTO models *)

Section CTO.
  Require Import String.
  Require Import Qcert.Utils.Utils.
  Require Import Qcert.Common.TypingRuntime.

  Require Import ErgoSpec.Backend.ErgoBackend.
  Require Import ErgoSpec.Common.Utils.ENames.

  Inductive cto_type :=
  | CTOBoolean : cto_type                             (**r bool atomic type *)
  | CTOString : cto_type                              (**r string atomic type *)
  | CTODouble : cto_type                              (**r double atomic type *)
  | CTOLong : cto_type                                (**r long atomic type *)
  | CTOInteger : cto_type                             (**r integer atomic type *)
  | CTODateTime : cto_type                            (**r date and time atomic type *)
  | CTOClassRef : class_ref -> cto_type               (**r class reference *)
  | CTOOption : cto_type -> cto_type                  (**r optional type *)
  | CTORecord : list (string*cto_type) -> cto_type    (**r record type *)
  | CTOArray : cto_type -> cto_type.                  (**r array type *)

  Inductive cto_declaration_kind :=
  | CTOEnum : list string -> cto_declaration_kind
  | CTOTransaction : option string -> list (string * cto_type) -> cto_declaration_kind
  | CTOConcept : option string -> list (string * cto_type) -> cto_declaration_kind.

  Record cto_declaration :=
    mkCTODeclaration
      { cto_declaration_class : class_ref;
        cto_declaration_type : cto_declaration_kind; }.

  Record cto_package :=
    mkCTOPackage
      { cto_package_namespace : string;
        cto_package_imports : list string;
        cto_package_declarations : list cto_declaration; }.

  Section Semantics.
    (** A semantics for CTO packages is obtained through translation
        into branded types. *)
    Program Fixpoint cto_type_to_etype {m:brand_relation} (scope:option string) (t:cto_type) : ErgoType.etype :=
      match t with
      | CTOBoolean => ErgoType.bool
      | CTOString => ErgoType.string
      | CTODouble => ErgoType.float
      | CTOLong => ErgoType.nat
      | CTOInteger => ErgoType.nat
      | CTODateTime => ErgoType.unit
      | CTOClassRef cr =>
        ErgoType.brand ((absolute_ref_of_class_ref scope cr)::nil)
      | CTOOption t =>
        ErgoType.option (cto_type_to_etype scope t)
      | CTORecord rtl =>
        ErgoType.record
          ErgoType.open_kind
          (rec_sort (List.map (fun xy => (fst xy, cto_type_to_etype scope (snd xy))) rtl))
          (rec_sort_sorted
             (List.map (fun xy => (fst xy, cto_type_to_etype scope (snd xy))) rtl)
             (rec_sort (List.map (fun xy => (fst xy, cto_type_to_etype scope (snd xy))) rtl))
             eq_refl)
      | CTOArray t =>
        ErgoType.bag (cto_type_to_etype scope t)
      end.

  End Semantics.
End CTO.
