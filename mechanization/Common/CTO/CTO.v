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

  Definition cto_class := string.

  Inductive cto_type :=
  | CTOString : cto_type                              (**r string atomic type *)
  | CTODouble : cto_type                              (**r double atomic type *)
  | CTOLong : cto_type                                (**r long atomic type *)
  | CTOBool : cto_type                                (**r bool atomic type *)
  | CTOClassRef : cto_class -> cto_type               (**r class reference *)
  | CTOOption : cto_type -> cto_type                  (**r optional type *)
  | CTOStructure : list (string*cto_type) -> cto_type (**r structure type *)
  | CTOArray : cto_type -> cto_type.                  (**r array type *)

  Inductive cto_declaration_kind :=
  | CTOEnum : list string -> cto_declaration_kind
  | CTOTransaction : option string -> list (string * cto_type) -> cto_declaration_kind
  | CTOConcept : option string -> list (string * cto_type) -> cto_declaration_kind.

  Record cto_declaration :=
    mkCTODeclaration
      { cto_declaration_class : cto_class;
        cto_declaration_type : cto_declaration_kind; }.

  Record cto_package :=
    mkCTOPackage
      { cto_package_namespace : string;
        cto_package_declarations : list cto_declaration; }.
End CTO.
