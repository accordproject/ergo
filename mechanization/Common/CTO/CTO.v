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

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EImport.

Section CTO.

  Inductive cto_type :=
  | CTOBoolean : cto_type                          (**r bool atomic type *)
  | CTOString : cto_type                           (**r string atomic type *)
  | CTODouble : cto_type                           (**r double atomic type *)
  | CTOLong : cto_type                             (**r long atomic type *)
  | CTOInteger : cto_type                          (**r integer atomic type *)
  | CTODateTime : cto_type                         (**r date and time atomic type *)
  | CTOClassRef : name_ref -> cto_type             (**r relative class reference *)
  | CTOOption : cto_type -> cto_type               (**r optional type *)
  | CTOArray : cto_type -> cto_type.               (**r array type *)

  Inductive cto_declaration_kind :=
  | CTOEnum : list string -> cto_declaration_kind
  | CTOTransaction : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOConcept : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOEvent : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOAsset : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOParticipant : option name_ref -> list (string * cto_type) -> cto_declaration_kind.

  Record cto_declaration :=
    mkCTODeclaration
      { cto_declaration_name : local_name;
        cto_declaration_type : cto_declaration_kind; }.

  Record cto_package :=
    mkCTOPackage
      { cto_package_namespace : namespace_name;
        cto_package_imports : list import_decl;
        cto_package_declarations : list cto_declaration; }.

End CTO.
