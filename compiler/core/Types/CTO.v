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

Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.

Section CTO.
  Section Ast.
    Context {A:Set}. (* Type for annotations *)
    Context {N:Set}. (* Type for names *)
  
    Inductive cto_type :=
    | CTOBoolean : A -> cto_type                   (**r bool atomic type *)
    | CTOString : A -> cto_type                    (**r string atomic type *)
    | CTODouble : A -> cto_type                    (**r double atomic type *)
    | CTOLong : A -> cto_type                      (**r long atomic type *)
    | CTOInteger : A -> cto_type                   (**r integer atomic type *)
    | CTODateTime : A -> cto_type                  (**r date and time atomic type *)
    | CTOClassRef : A -> N -> cto_type             (**r relative class reference *)
    | CTOOption : A -> cto_type -> cto_type        (**r optional type *)
    | CTOArray : A -> cto_type -> cto_type         (**r array type *)
    .

    Definition cto_annot (ct:cto_type) : A :=
      match ct with
      | CTOBoolean a => a
      | CTOString a => a
      | CTODouble a => a
      | CTOLong a => a
      | CTOInteger a => a
      | CTODateTime a => a
      | CTOClassRef a _ => a
      | CTOOption a _ => a
      | CTOArray a _ => a
      end.

    Inductive cto_declaration_desc :=
    | CTOEnum : list string -> cto_declaration_desc
    | CTOTransaction : is_abstract -> @extends N -> list (string * cto_type) -> cto_declaration_desc
    | CTOConcept : is_abstract -> @extends N -> list (string * cto_type) -> cto_declaration_desc
    | CTOEvent : is_abstract -> @extends N -> list (string * cto_type) -> cto_declaration_desc
    | CTOAsset : is_abstract -> @extends N -> list (string * cto_type) -> cto_declaration_desc
    | CTOParticipant : is_abstract -> @extends N -> list (string * cto_type) -> cto_declaration_desc.

    Record cto_declaration :=
      mkCTODeclaration
        { cto_declaration_annot : A;
          cto_declaration_name : local_name;
          cto_declaration_type : cto_declaration_desc; }.

    Record cto_package :=
      mkCTOPackage
        { cto_package_annot : A;
          cto_package_file : string;
          cto_package_prefix : string;
          cto_package_namespace : namespace_name;
          cto_package_imports : list (@import_decl A);
          cto_package_declarations : list cto_declaration; }.
  End Ast.

  Definition rcto_type {A:Set} : Set := @cto_type A relative_name.
  Definition rcto_declaration_desc {A:Set} : Set := @cto_declaration_desc A relative_name.
  Definition rcto_declaration {A:Set} : Set := @cto_declaration A relative_name.
  Definition rcto_package {A:Set} : Set := @cto_package A relative_name.
  
  Definition lrcto_type : Set := @cto_type provenance relative_name.
  Definition lrcto_declaration_desc : Set := @cto_declaration_desc provenance relative_name.
  Definition lrcto_declaration : Set := @cto_declaration provenance relative_name.
  Definition lrcto_package : Set := @cto_package provenance relative_name.

End CTO.

