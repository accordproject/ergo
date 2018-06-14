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
Require Import ErgoSpec.Common.Utils.EImport.

Section CTO.

  Inductive cto_type :=
  | CTOAny : cto_type                              (**r any type *)
  | CTONone : cto_type                             (**r none type *)
  | CTOBoolean : cto_type                          (**r bool atomic type *)
  | CTOString : cto_type                           (**r string atomic type *)
  | CTODouble : cto_type                           (**r double atomic type *)
  | CTOLong : cto_type                             (**r long atomic type *)
  | CTOInteger : cto_type                          (**r integer atomic type *)
  | CTODateTime : cto_type                         (**r date and time atomic type *)
  | CTOClassRef : name_ref -> cto_type             (**r relative class reference *)
  | CTOOption : cto_type -> cto_type               (**r optional type *)
  | CTORecord : list (string*cto_type) -> cto_type (**r record type *)
  | CTOArray : cto_type -> cto_type.               (**r array type *)

  Record cto_signature : Set :=
    mkCTOSignature
      { cto_signature_name: string;
        cto_signature_params : list (string * cto_type);
        cto_signature_output : cto_type;
        cto_signature_throws : option cto_type;
        cto_signature_emits : option cto_type }.

  Inductive cto_declaration_kind :=
  | CTOEnum : list string -> cto_declaration_kind
  | CTOTransaction : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOConcept : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOEvent : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOAsset : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOParticipant : option name_ref -> list (string * cto_type) -> cto_declaration_kind
  | CTOGlobal : cto_type -> cto_declaration_kind
  | CTOFunction : cto_signature -> cto_declaration_kind
  | CTOContract :
      cto_type                         (**r template type *)
      -> list (string * cto_signature) (**r clauses signatures *)
      -> cto_declaration_kind.

  Record cto_declaration :=
    mkCTODeclaration
      { cto_declaration_name : local_name;
        cto_declaration_type : cto_declaration_kind; }.

  Record cto_package :=
    mkCTOPackage
      { cto_package_namespace : namespace_name;
        cto_package_imports : list import_decl;
        cto_package_declarations : list cto_declaration; }.

  Section NamesResolution.
    (** There are three phases to the name resolution in CTO files/packages:
- build a per-namespace table containing all the local names mapped to their namespace resolve names
- for a package, resolve imports using the per-namespace table to build a full namespace mapping for that package
- resolve the names within a given package using the full namespace mapping for that package *)
    
    (** Maps local names to absolute names for a given CTO package *)
    Definition cto_names_table : Set := list (local_name * absolute_name).

    (** Maps namespaces to the names table for that namespace *)
    Definition cto_names_tables : Set := list (namespace_name * cto_names_table).

    Definition name_entry_of_cto_declaration (ns:namespace_name) (decl:cto_declaration) : local_name * absolute_name :=
      let ln := decl.(cto_declaration_name) in
      (ln, absolute_name_of_local_name ns ln).

    Definition names_table_of_cto_package (ns:namespace_name) (pkg:cto_package) : cto_names_table :=
      map (name_entry_of_cto_declaration ns) pkg.(cto_package_declarations).

    (** Note: this merges tables when the same namespace is used in more than one CTO package *)
    Definition names_tables_of_cto_packages (pkgs: list cto_package) : cto_names_tables :=
      let init : cto_names_tables := nil in
      let proc_one (acc:cto_names_tables) (pkg:cto_package) : cto_names_tables :=
          let ns := pkg.(cto_package_namespace) in
          match lookup string_dec acc ns with
          | Some t =>
            update_first string_dec acc ns (app t (names_table_of_cto_package ns pkg))
          | None =>
            (ns, names_table_of_cto_package ns pkg) :: acc
          end
      in
      fold_left proc_one pkgs init.

    (** This applies imports *)
    Definition apply_import_to_names
               (ns:namespace_name)
               (ic:import_criteria)
               (tbl:cto_names_table) : eresult cto_names_table :=
      match ic with
      | ImportAll => esuccess tbl
      | ImportName n =>
        match lookup string_dec tbl n with
        | None => import_name_not_found ns n
        | Some t => esuccess ((n,t)::nil)
        end
      end.

    Definition apply_imports_to_names_tables
               (ns:namespace_name)
               (tbls:cto_names_tables)
               (imports:list import_decl) : eresult cto_names_table :=
      let init : eresult cto_names_table := esuccess nil in
      let proc_one (acc:eresult cto_names_table) (import:import_decl) : eresult cto_names_table :=
          match lookup string_dec tbls (fst import) with
          | Some t =>
            elift2 (fun x y => app x y)
                   acc
                   (apply_import_to_names ns (snd import) t)
          | None => import_not_found (fst import)
          end
      in
      fold_left proc_one imports init.

    (** Local name lookup *)
    Definition local_name_resolution (module_ns:namespace_name) (tbl:cto_names_table) (nr:name_ref) : eresult absolute_name :=
      match nr with
      | RelativeRef None ln =>
        match lookup string_dec tbl ln with
        | None => resolve_name_not_found module_ns ln
        | Some an => esuccess an
        end
      | RelativeRef (Some ns) ln =>
        esuccess  (absolute_name_of_local_name ns ln)
      | AbsoluteRef an =>
        esuccess an
      end.

    (** This is the name resolution *)
    Fixpoint resolve_cto_type (module_ns:namespace_name) (tbl:cto_names_table) (t:cto_type) : eresult cto_type :=
      match t with
      | CTOAny => esuccess CTOAny
      | CTONone => esuccess CTONone
      | CTOBoolean => esuccess CTOBoolean
      | CTOString => esuccess CTOString
      | CTODouble => esuccess CTODouble
      | CTOLong => esuccess CTOLong
      | CTOInteger => esuccess CTOInteger
      | CTODateTime => esuccess CTODateTime
      | CTOClassRef r => elift CTOClassRef (elift AbsoluteRef (local_name_resolution module_ns tbl r))
      | CTOOption t => elift CTOOption (resolve_cto_type module_ns tbl t)
      | CTORecord r =>
        let initial_map := map (fun xy => (fst xy, resolve_cto_type module_ns tbl (snd xy))) r in
        let lifted_map := emaplift (fun xy => elift (fun t => (fst xy, t)) (snd xy)) initial_map in
        elift CTORecord lifted_map
      | CTOArray t => elift CTOArray (resolve_cto_type module_ns tbl t)
      end.

    Definition resolve_cto_struct
               (ns:namespace_name)
               (tbl:cto_names_table)
               (t:list (string * cto_type)) : eresult (list (string * cto_type)) :=
      emaplift (fun xy =>
                  elift (fun t => (fst xy, t)) (resolve_cto_type ns tbl (snd xy))) t.

    Definition resolve_extends_name
               (ns:string) (tbl:cto_names_table) (en:option name_ref) : eresult (option name_ref) :=
      match en with
      | None => esuccess None
      | Some ln => elift Some (elift AbsoluteRef (local_name_resolution ns tbl ln))
      end.

    Definition resolve_cto_signature
               (ns:namespace_name)
               (tbl:cto_names_table)
               (sig:cto_signature) :=
      let params_types := resolve_cto_struct ns tbl (sig.(cto_signature_params)) in
      let output_type := resolve_cto_type ns tbl sig.(cto_signature_output) in
      let throws_type :=
          match sig.(cto_signature_throws) with
          | None => esuccess None
          | Some throw_ty =>
            elift Some (resolve_cto_type ns tbl throw_ty)
          end
      in
      let emits_type :=
          match sig.(cto_signature_emits) with
          | None => esuccess None
          | Some throw_ty =>
            elift Some (resolve_cto_type ns tbl throw_ty)
          end
      in
      elift4 (mkCTOSignature
                sig.(cto_signature_name))
             params_types
             output_type
             throws_type
             emits_type.

    Definition resolve_cto_clauses
               (ns:namespace_name)
               (tbl:cto_names_table)
               (cls:list (string * cto_signature)) : eresult (list (string * cto_signature)) :=
      emaplift (fun xy => elift (fun r => (fst xy, r))
                                (resolve_cto_signature ns tbl (snd xy))) cls.

    Definition resolve_decl_kind (module_ns:namespace_name) (tbl:cto_names_table)
               (k:cto_declaration_kind) : eresult cto_declaration_kind :=
      match k with
      | CTOEnum l => esuccess (CTOEnum l)
      | CTOTransaction extends_name cto_struct =>
        elift2 CTOTransaction
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_cto_struct module_ns tbl cto_struct)
      | CTOConcept extends_name cto_struct =>
        elift2 CTOConcept
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_cto_struct module_ns tbl cto_struct)
      | CTOEvent extends_name cto_struct =>
        elift2 CTOEvent
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_cto_struct module_ns tbl cto_struct)
      | CTOAsset extends_name cto_struct =>
        elift2 CTOAsset
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_cto_struct module_ns tbl cto_struct)
      | CTOParticipant extends_name cto_struct =>
        elift2 CTOParticipant
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_cto_struct module_ns tbl cto_struct)
      | CTOGlobal cto_type =>
        elift CTOGlobal (resolve_cto_type module_ns tbl cto_type)
      | CTOFunction cto_signature =>
        elift CTOFunction
              (resolve_cto_signature module_ns tbl cto_signature)
      | CTOContract template_type clauses_sigs =>
        elift2 CTOContract
               (resolve_cto_type module_ns tbl template_type)
               (resolve_cto_clauses module_ns tbl clauses_sigs)
      end.

    Definition resolve_declaration (module_ns:namespace_name) (tbl:cto_names_table) (decl: cto_declaration) : eresult cto_declaration :=
      let name := absolute_name_of_local_name module_ns decl.(cto_declaration_name) in
      let edecl_kind := resolve_decl_kind module_ns tbl decl.(cto_declaration_type) in
      elift (fun k => mkCTODeclaration name k) edecl_kind.
    
    Definition resolve_declarations (module_ns:namespace_name) (tbl:cto_names_table) (decls: list cto_declaration)
      : eresult (list cto_declaration) :=
      emaplift (resolve_declaration module_ns tbl) decls.

    Definition resolve_names_in_package
               (tbls:cto_names_tables)
               (pkg:cto_package) : eresult (list cto_declaration) :=
      (** Make sure to add current namespace to the list of imports - i.e., import self. *)
      let imports := app pkg.(cto_package_imports)
                               (("org.hyperledger.composer.system"%string, ImportAll)
                                  ::(pkg.(cto_package_namespace),ImportAll)::nil) in
      let module_ns := pkg.(cto_package_namespace) in
      let in_scope_names := apply_imports_to_names_tables module_ns tbls imports in
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

  Section SampleCTO.
    Local Open Scope string.
    Definition ctod1 :=
      mkCTODeclaration "c1" (CTOConcept None (("a", CTOBoolean)::("b",CTOClassRef (RelativeRef None "c3"))::nil)).
    
    Definition ctod2 :=
      mkCTODeclaration "c2" (CTOConcept None (("c", CTOBoolean)::("d",CTOClassRef (RelativeRef None "c1"))::nil)).
    

    Definition cto1 :=
      mkCTOPackage
        "n1" (("n2",ImportAll)::nil) (ctod1::ctod2::nil).
    
    Definition ctod3 :=
      mkCTODeclaration "c3" (CTOConcept None (("a", CTOBoolean)::("b",CTOString)::nil)).
    
    Definition cto2 :=
      mkCTOPackage
        "n2" nil (ctod3::nil).

    Definition pkgs := cto2 :: cto1 :: nil.

    Definition tbls := names_tables_of_cto_packages pkgs.
    (* Eval vm_compute in tbls. *)
    Definition res := elift (@List.concat _) (emaplift (resolve_names_in_package tbls) pkgs).
    (* Eval vm_compute in res. *)
  End SampleCTO.
    
  Section Semantics.
    (** A semantics for CTO packages is obtained through translation
        into branded types. *)
    Program Fixpoint cto_type_to_etype {m:brand_relation} (t:cto_type) : ErgoType.etype :=
      match t with
      | CTOAny => ErgoType.top
      | CTONone => ErgoType.empty
      | CTOBoolean => ErgoType.bool
      | CTOString => ErgoType.string
      | CTODouble => ErgoType.double
      | CTOLong => ErgoType.integer (* XXX To be decided *)
      | CTOInteger => ErgoType.integer
      | CTODateTime => ErgoType.empty (* XXX TBD *)
      | CTOClassRef cr =>
        ErgoType.brand (absolute_name_of_name_ref "UNKNOWN.NAMESPACE"%string cr::nil)
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
        ErgoType.array (cto_type_to_etype t)
      end.

  End Semantics.

End CTO.
