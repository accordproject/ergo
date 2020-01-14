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

(** Translates a CTO to an Ergo module *)

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section CTOtoErgo.

  Fixpoint cto_type_to_ergo_type (ctd:lrcto_type) : lrergo_type :=
    match ctd with
    | CTOBoolean loc => ErgoTypeBoolean loc
    | CTOString loc => ErgoTypeString loc
    | CTODouble loc => ErgoTypeDouble loc
    | CTOLong loc => ErgoTypeLong loc
    | CTOInteger loc => ErgoTypeInteger loc
    | CTODateTime loc => ErgoTypeDateTime loc
    | CTOClassRef loc n => ErgoTypeClassRef loc n
    | CTOOption loc ct1 => ErgoTypeOption loc (cto_type_to_ergo_type ct1)
    | CTOArray loc ct1 => ErgoTypeArray loc (cto_type_to_ergo_type ct1)
    end.

  Definition cto_declaration_desc_to_ergo_type_declaration_desc
             (dk:lrcto_declaration_desc) : lrergo_type_declaration_desc :=
    match dk with
    | CTOEnum ls => ErgoTypeEnum ls
    | CTOTransaction on isabs crec =>
      ErgoTypeTransaction on isabs (map (fun xy => (fst xy, cto_type_to_ergo_type (snd xy))) crec)
    | CTOConcept on isabs crec =>
      ErgoTypeConcept on isabs (map (fun xy => (fst xy, cto_type_to_ergo_type (snd xy))) crec)
    | CTOEvent on isabs crec =>
      ErgoTypeEvent on isabs (map (fun xy => (fst xy, cto_type_to_ergo_type (snd xy))) crec)
    | CTOAsset on isabs crec =>
      ErgoTypeAsset on isabs (map (fun xy => (fst xy, cto_type_to_ergo_type (snd xy))) crec)
    | CTOParticipant on isabs crec =>
      ErgoTypeParticipant on isabs (map (fun xy => (fst xy, cto_type_to_ergo_type (snd xy))) crec)
    end.  

  Definition cto_declaration_to_ergo_type_declaration (d:lrcto_declaration) : lrergo_type_declaration :=
    mkErgoTypeDeclaration
      d.(cto_declaration_annot)
      d.(cto_declaration_name)
      (cto_declaration_desc_to_ergo_type_declaration_desc d.(cto_declaration_type)).

  Definition cto_declaration_to_ergo_declaration (d:lrcto_declaration) : lrergo_declaration :=
    DType d.(cto_declaration_annot) (cto_declaration_to_ergo_type_declaration d).
  Definition cto_import_to_ergo_declaration (d:import_decl) : lrergo_declaration :=
    DImport (import_annot d) d.

  Definition cto_package_to_ergo_module (p:lrcto_package) : lrergo_module :=
    mkModule
      p.(cto_package_annot)
      p.(cto_package_file)
      p.(cto_package_prefix)
      p.(cto_package_namespace)
      ((map cto_import_to_ergo_declaration p.(cto_package_imports))
       ++ (map cto_declaration_to_ergo_declaration p.(cto_package_declarations))).

End CTOtoErgo.
