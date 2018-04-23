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
Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.TypingRuntime.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EError.
Require Import ErgoSpec.Common.Utils.EImport.

Section CTO.

  Inductive cto_type :=
  | CTOBoolean : cto_type                             (**r bool atomic type *)
  | CTOString : cto_type                              (**r string atomic type *)
  | CTODouble : cto_type                              (**r double atomic type *)
  | CTOLong : cto_type                                (**r long atomic type *)
  | CTOInteger : cto_type                             (**r integer atomic type *)
  | CTODateTime : cto_type                            (**r date and time atomic type *)
  | CTOClassRef : string -> cto_type                  (**r class reference *)
  | CTOOption : cto_type -> cto_type                  (**r optional type *)
  | CTORecord : list (string*cto_type) -> cto_type    (**r record type *)
  | CTOArray : cto_type -> cto_type.                  (**r array type *)

  Inductive cto_declaration_kind :=
  | CTOEnum : list string -> cto_declaration_kind
  | CTOTransaction : option string -> list (string * cto_type) -> cto_declaration_kind
  | CTOConcept : option string -> list (string * cto_type) -> cto_declaration_kind.

  Record cto_declaration :=
    mkCTODeclaration
      { cto_declaration_class : string;
        cto_declaration_type : cto_declaration_kind; }.

  Record cto_package :=
    mkCTOPackage
      { cto_package_namespace : string;
        cto_package_imports : list import_decl;
        cto_package_declarations : list cto_declaration; }.

  Section NamesResolution.
    (** There are three phases to the name resolution in CTO files/packages:
- build a per-namespace table containing all the local names mapped to their namespace resolve names
- for a package, resolve imports using the per-namespace table to build a full namespace mapping for that package
- resolve the names within a given package using the full namespace mapping for that package *)
    
    (** Maps relative names to absolute names for a given CTO package *)
    Definition cto_names_table : Set := list (string * string).

    (** Maps namespaces to the names table for that namespace *)
    Definition cto_names_tables : Set := list (string * cto_names_table).

    Definition name_entry_of_cto_declaration (namespace:string) (decl:cto_declaration) : string * string :=
      let relative_ref := decl.(cto_declaration_class) in
      (relative_ref, absolute_ref_of_relative_ref namespace relative_ref).

    Definition names_table_of_cto_package (namespace:string) (pkg:cto_package) : cto_names_table :=
      map (name_entry_of_cto_declaration namespace) pkg.(cto_package_declarations).

    (** Note: this merges tables when the same namespace is used in more than one CTO package *)
    Definition names_tables_of_cto_packages (pkgs: list cto_package) : cto_names_tables :=
      let init : cto_names_tables := nil in
      let proc_one (acc:cto_names_tables) (pkg:cto_package) : cto_names_tables :=
          let namespace := pkg.(cto_package_namespace) in
          match lookup string_dec acc namespace with
          | Some t =>
            update_first string_dec acc namespace (app t (names_table_of_cto_package namespace pkg))
          | None =>
            (namespace, names_table_of_cto_package namespace pkg) :: acc
          end
      in
      fold_left proc_one pkgs init.

    (** This applies imports *)
    Definition apply_import_to_names
               (namespace:string)
               (ic:import_criteria)
               (tbl:cto_names_table) : eresult cto_names_table :=
      match ic with
      | ImportAll => esuccess tbl
      | ImportName n =>
        match lookup string_dec tbl n with
        | None => import_name_not_found namespace n
        | Some t => esuccess ((n,t)::nil)
        end
      end.

    Definition apply_imports_to_names_tables
               (namespace:string)
               (tbls:cto_names_tables)
               (imports:list import_decl) : eresult cto_names_table :=
      let init : eresult cto_names_table := esuccess nil in
      let proc_one (acc:eresult cto_names_table) (import:import_decl) : eresult cto_names_table :=
          match lookup string_dec tbls (fst import) with
          | Some t =>
            elift2 (fun x y => app x y)
                   acc
                   (apply_import_to_names namespace (snd import) t)
          | None => import_not_found (fst import)
          end
      in
      fold_left proc_one imports init.

    (** Local name lookup *)
    Definition local_name_lookup (namespace:string) (tbl:cto_names_table) (name_ref:string) :=
      match lookup string_dec tbl name_ref with
      | None => resolve_name_not_found namespace name_ref
      | Some n => esuccess n
      end.
    
    (** This is the name resolution *)
    Definition resolve_cto_type (namespace:string) (tbl:cto_names_table) (t:cto_type) : eresult cto_type :=
      esuccess t.
    Definition resolve_cto_struct
               (namespace:string)
               (tbl:cto_names_table)
               (t:list (string * cto_type)) : eresult (list (string * cto_type)) :=
      esuccess t.

    Definition resolve_extend_name
               (namespace:string) (tbl:cto_names_table) (extend_name:option string) : eresult (option string) :=
      match extend_name with
      | None => esuccess None
      | Some n => elift Some (local_name_lookup namespace tbl n)
      end.

    Definition resolve_decl_kind (namespace:string) (tbl:cto_names_table)
               (k:cto_declaration_kind) : eresult cto_declaration_kind :=
      match k with
      | CTOEnum l => esuccess (CTOEnum l)
      | CTOTransaction extend_name cto_struct =>
        elift2 (fun x y => CTOTransaction x y)
               (resolve_extend_name namespace tbl extend_name)
               (resolve_cto_struct namespace tbl cto_struct)
      | CTOConcept extend_name cto_struct =>
        elift2 (fun x y => CTOConcept x y)
               (resolve_extend_name namespace tbl extend_name)
               (resolve_cto_struct namespace tbl cto_struct)
      end.

    Definition resolve_declaration (namespace:string) (tbl:cto_names_table) (decl: cto_declaration) : eresult cto_declaration :=
      let name := absolute_ref_of_relative_ref namespace decl.(cto_declaration_class) in
      let edecl_kind := resolve_decl_kind namespace tbl decl.(cto_declaration_type) in
      elift (fun k => mkCTODeclaration name k) edecl_kind.
    
    Definition resolve_declarations (namespace:string) (tbl:cto_names_table) (decls: list cto_declaration)
      : eresult (list cto_declaration) :=
      emaplift (resolve_declaration namespace tbl) decls.

    Definition resolve_names_in_package
               (tbls:cto_names_tables)
               (pkg:cto_package) : eresult (list cto_declaration) :=
      let imports := pkg.(cto_package_imports) in
      let namespace := pkg.(cto_package_namespace) in
      let in_scope_names := apply_imports_to_names_tables namespace tbls imports in
      eolift (fun tbls => resolve_declarations
                            pkg.(cto_package_namespace)
                            tbls
                            pkg.(cto_package_declarations)) in_scope_names.

    (** Top level *)
    Definition cto_resolved_tbl_for_package
               (pkgs:list cto_package) : eresult (list cto_declaration) :=
      let tbls := names_tables_of_cto_packages pkgs in
      elift (@List.concat _) (emaplift (resolve_names_in_package tbls) pkgs).

  End NamesResolution.
  
  Section Semantics.
    (** A semantics for CTO packages is obtained through translation
        into branded types. *)
    Program Fixpoint cto_type_to_etype {m:brand_relation} (t:cto_type) : ErgoType.etype :=
      match t with
      | CTOBoolean => ErgoType.bool
      | CTOString => ErgoType.string
      | CTODouble => ErgoType.float
      | CTOLong => ErgoType.nat
      | CTOInteger => ErgoType.nat
      | CTODateTime => ErgoType.unit
      | CTOClassRef cr =>
        ErgoType.brand (cr::nil)
      | CTOOption t =>
        ErgoType.option (cto_type_to_etype t)
      | CTORecord rtl =>
        ErgoType.record
          ErgoType.open_kind
          (rec_sort (List.map (fun xy => (fst xy, cto_type_to_etype (snd xy))) rtl))
          (rec_sort_sorted
             (List.map (fun xy => (fst xy, cto_type_to_etype (snd xy))) rtl)
             (rec_sort (List.map (fun xy => (fst xy, cto_type_to_etype (snd xy))) rtl))
             eq_refl)
      | CTOArray t =>
        ErgoType.bag (cto_type_to_etype t)
      end.

  End Semantics.
End CTO.
