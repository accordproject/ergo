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

Section ErgoType.

  Inductive ergo_type :=
  | ErgoTypeAny : ergo_type                               (**r any type *)
  | ErgoTypeNone : ergo_type                              (**r none type *)
  | ErgoTypeBoolean : ergo_type                           (**r bool atomic type *)
  | ErgoTypeString : ergo_type                            (**r string atomic type *)
  | ErgoTypeDouble : ergo_type                            (**r double atomic type *)
  | ErgoTypeLong : ergo_type                              (**r long atomic type *)
  | ErgoTypeInteger : ergo_type                           (**r integer atomic type *)
  | ErgoTypeDateTime : ergo_type                          (**r date and time atomic type *)
  | ErgoTypeClassRef : name_ref -> ergo_type              (**r relative class reference *)
  | ErgoTypeOption : ergo_type -> ergo_type               (**r optional type *)
  | ErgoTypeRecord : list (string*ergo_type) -> ergo_type (**r record type *)
  | ErgoTypeArray : ergo_type -> ergo_type                (**r array type *)
  | ErgoTypeSum : ergo_type -> ergo_type -> ergo_type.    (**r sum type *)

  Record ergo_type_signature : Set :=
    mkErgoTypeSignature
      { ergo_type_signature_name: string;
        ergo_type_signature_params : list (string * ergo_type);
        ergo_type_signature_output : ergo_type;
        ergo_type_signature_throws : option ergo_type;
        ergo_type_signature_emits : option ergo_type }.

  Inductive ergo_type_declaration_kind :=
  | ErgoTypeEnum : list string -> ergo_type_declaration_kind
  | ErgoTypeTransaction : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_kind
  | ErgoTypeConcept : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_kind
  | ErgoTypeEvent : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_kind
  | ErgoTypeAsset : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_kind
  | ErgoTypeParticipant : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_kind
  | ErgoTypeGlobal : ergo_type -> ergo_type_declaration_kind
  | ErgoTypeFunction : ergo_type_signature -> ergo_type_declaration_kind
  | ErgoTypeContract :
      ergo_type                              (**r template type *)
      -> ergo_type                           (**r state type *)
      -> list (string * ergo_type_signature) (**r clauses signatures *)
      -> ergo_type_declaration_kind.

  Record ergo_type_declaration :=
    mkErgoTypeDeclaration
      { ergo_type_declaration_name : local_name;
        ergo_type_declaration_type : ergo_type_declaration_kind; }.

  Record ergo_type_module :=
    mkErgoTypeModule
      { ergo_type_module_namespace : namespace_name;
        ergo_type_module_imports : list import_decl;
        ergo_type_module_declarations : list ergo_type_declaration; }.

  Section NamesResolution.
    (** There are three phases to the name resolution in ErgoType files/modules:
- build a per-namespace table containing all the local names mapped to their namespace resolve names
- for a module, resolve imports using the per-namespace table to build a full namespace mapping for that module
- resolve the names within a given module using the full namespace mapping for that module *)
    
    (** Maps local names to absolute names for a given ErgoType module *)
    Definition ergo_type_names_table : Set := list (local_name * absolute_name).

    (** Maps namespaces to the names table for that namespace *)
    Definition ergo_type_names_tables : Set := list (namespace_name * ergo_type_names_table).

    Definition name_entry_of_ergo_type_declaration (ns:namespace_name) (decl:ergo_type_declaration) : local_name * absolute_name :=
      let ln := decl.(ergo_type_declaration_name) in
      (ln, absolute_name_of_local_name ns ln).

    Definition names_table_of_ergo_type_module (ns:namespace_name) (pkg:ergo_type_module) : ergo_type_names_table :=
      map (name_entry_of_ergo_type_declaration ns) pkg.(ergo_type_module_declarations).

    (** Note: this merges tables when the same namespace is used in more than one ErgoType module *)
    Definition names_tables_of_ergo_type_modules (pkgs: list ergo_type_module) : ergo_type_names_tables :=
      let init : ergo_type_names_tables := nil in
      let proc_one (acc:ergo_type_names_tables) (pkg:ergo_type_module) : ergo_type_names_tables :=
          let ns := pkg.(ergo_type_module_namespace) in
          match lookup string_dec acc ns with
          | Some t =>
            update_first string_dec acc ns (app t (names_table_of_ergo_type_module ns pkg))
          | None =>
            (ns, names_table_of_ergo_type_module ns pkg) :: acc
          end
      in
      fold_left proc_one pkgs init.

    (** This applies imports *)
    Definition apply_import_to_names
               (ns:namespace_name)
               (ic:import_criteria)
               (tbl:ergo_type_names_table) : eresult ergo_type_names_table :=
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
               (tbls:ergo_type_names_tables)
               (imports:list import_decl) : eresult ergo_type_names_table :=
      let init : eresult ergo_type_names_table := esuccess nil in
      let proc_one (acc:eresult ergo_type_names_table) (import:import_decl) : eresult ergo_type_names_table :=
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
    Definition local_name_resolution (module_ns:namespace_name) (tbl:ergo_type_names_table) (nr:name_ref) : eresult absolute_name :=
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
    Fixpoint resolve_ergo_type (module_ns:namespace_name) (tbl:ergo_type_names_table) (t:ergo_type) : eresult ergo_type :=
      match t with
      | ErgoTypeAny => esuccess ErgoTypeAny
      | ErgoTypeNone => esuccess ErgoTypeNone
      | ErgoTypeBoolean => esuccess ErgoTypeBoolean
      | ErgoTypeString => esuccess ErgoTypeString
      | ErgoTypeDouble => esuccess ErgoTypeDouble
      | ErgoTypeLong => esuccess ErgoTypeLong
      | ErgoTypeInteger => esuccess ErgoTypeInteger
      | ErgoTypeDateTime => esuccess ErgoTypeDateTime
      | ErgoTypeClassRef r => elift ErgoTypeClassRef (elift AbsoluteRef (local_name_resolution module_ns tbl r))
      | ErgoTypeOption t => elift ErgoTypeOption (resolve_ergo_type module_ns tbl t)
      | ErgoTypeRecord r =>
        let initial_map := map (fun xy => (fst xy, resolve_ergo_type module_ns tbl (snd xy))) r in
        let lifted_map := emaplift (fun xy => elift (fun t => (fst xy, t)) (snd xy)) initial_map in
        elift ErgoTypeRecord lifted_map
      | ErgoTypeArray t => elift ErgoTypeArray (resolve_ergo_type module_ns tbl t)
      | ErgoTypeSum t1 t2 => elift2 ErgoTypeSum (resolve_ergo_type module_ns tbl t1) (resolve_ergo_type module_ns tbl t2)
      end.

    Definition resolve_ergo_type_struct
               (ns:namespace_name)
               (tbl:ergo_type_names_table)
               (t:list (string * ergo_type)) : eresult (list (string * ergo_type)) :=
      emaplift (fun xy =>
                  elift (fun t => (fst xy, t)) (resolve_ergo_type ns tbl (snd xy))) t.

    Definition resolve_extends_name
               (ns:string) (tbl:ergo_type_names_table) (en:option name_ref) : eresult (option name_ref) :=
      match en with
      | None => esuccess None
      | Some ln => elift Some (elift AbsoluteRef (local_name_resolution ns tbl ln))
      end.

    Definition resolve_ergo_type_signature
               (ns:namespace_name)
               (tbl:ergo_type_names_table)
               (sig:ergo_type_signature) :=
      let params_types := resolve_ergo_type_struct ns tbl (sig.(ergo_type_signature_params)) in
      let output_type := resolve_ergo_type ns tbl sig.(ergo_type_signature_output) in
      let throws_type :=
          match sig.(ergo_type_signature_throws) with
          | None => esuccess None
          | Some throw_ty =>
            elift Some (resolve_ergo_type ns tbl throw_ty)
          end
      in
      let emits_type :=
          match sig.(ergo_type_signature_emits) with
          | None => esuccess None
          | Some throw_ty =>
            elift Some (resolve_ergo_type ns tbl throw_ty)
          end
      in
      elift4 (mkErgoTypeSignature
                sig.(ergo_type_signature_name))
             params_types
             output_type
             throws_type
             emits_type.

    Definition resolve_ergo_type_clauses
               (ns:namespace_name)
               (tbl:ergo_type_names_table)
               (cls:list (string * ergo_type_signature)) : eresult (list (string * ergo_type_signature)) :=
      emaplift (fun xy => elift (fun r => (fst xy, r))
                                (resolve_ergo_type_signature ns tbl (snd xy))) cls.

    Definition resolve_decl_kind (module_ns:namespace_name) (tbl:ergo_type_names_table)
               (k:ergo_type_declaration_kind) : eresult ergo_type_declaration_kind :=
      match k with
      | ErgoTypeEnum l => esuccess (ErgoTypeEnum l)
      | ErgoTypeTransaction extends_name ergo_type_struct =>
        elift2 ErgoTypeTransaction
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
      | ErgoTypeConcept extends_name ergo_type_struct =>
        elift2 ErgoTypeConcept
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
      | ErgoTypeEvent extends_name ergo_type_struct =>
        elift2 ErgoTypeEvent
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
      | ErgoTypeAsset extends_name ergo_type_struct =>
        elift2 ErgoTypeAsset
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
      | ErgoTypeParticipant extends_name ergo_type_struct =>
        elift2 ErgoTypeParticipant
               (resolve_extends_name module_ns tbl extends_name)
               (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
      | ErgoTypeGlobal ergo_type =>
        elift ErgoTypeGlobal (resolve_ergo_type module_ns tbl ergo_type)
      | ErgoTypeFunction ergo_type_signature =>
        elift ErgoTypeFunction
              (resolve_ergo_type_signature module_ns tbl ergo_type_signature)
      | ErgoTypeContract template_type state_type clauses_sigs =>
        elift3 ErgoTypeContract
               (resolve_ergo_type module_ns tbl template_type)
               (resolve_ergo_type module_ns tbl state_type)
               (resolve_ergo_type_clauses module_ns tbl clauses_sigs)
      end.

    Definition resolve_declaration (module_ns:namespace_name) (tbl:ergo_type_names_table) (decl: ergo_type_declaration) : eresult ergo_type_declaration :=
      let name := absolute_name_of_local_name module_ns decl.(ergo_type_declaration_name) in
      let edecl_kind := resolve_decl_kind module_ns tbl decl.(ergo_type_declaration_type) in
      elift (fun k => mkErgoTypeDeclaration name k) edecl_kind.
    
    Definition resolve_declarations (module_ns:namespace_name) (tbl:ergo_type_names_table) (decls: list ergo_type_declaration)
      : eresult (list ergo_type_declaration) :=
      emaplift (resolve_declaration module_ns tbl) decls.

    Definition resolve_names_in_module
               (tbls:ergo_type_names_tables)
               (pkg:ergo_type_module) : eresult (list ergo_type_declaration) :=
      (** Make sure to add current namespace to the list of imports - i.e., import self. *)
      let imports := app pkg.(ergo_type_module_imports)
                               (("org.hyperledger.composer.system"%string, ImportAll)
                                  ::(pkg.(ergo_type_module_namespace),ImportAll)::nil) in
      let module_ns := pkg.(ergo_type_module_namespace) in
      let in_scope_names := apply_imports_to_names_tables module_ns tbls imports in
      eolift (fun tbls => resolve_declarations
                            pkg.(ergo_type_module_namespace)
                            tbls
                            pkg.(ergo_type_module_declarations)) in_scope_names.

    (** Top level *)
    Definition ergo_type_resolved_tbl_for_module
               (pkgs:list ergo_type_module) : eresult (list ergo_type_declaration) :=
      let tbls := names_tables_of_ergo_type_modules pkgs in
      elift (@List.concat _) (emaplift (resolve_names_in_module tbls) pkgs).

  End NamesResolution.

  Section Examples.
    Local Open Scope string.
    Definition ergo_typed1 :=
      mkErgoTypeDeclaration "c1" (ErgoTypeConcept None (("a", ErgoTypeBoolean)::("b",ErgoTypeClassRef (RelativeRef None "c3"))::nil)).
    
    Definition ergo_typed2 :=
      mkErgoTypeDeclaration "c2" (ErgoTypeConcept None (("c", ErgoTypeBoolean)::("d",ErgoTypeClassRef (RelativeRef None "c1"))::nil)).
    

    Definition ergo_type1 :=
      mkErgoTypeModule
        "n1" (("n2",ImportAll)::nil) (ergo_typed1::ergo_typed2::nil).
    
    Definition ergo_typed3 :=
      mkErgoTypeDeclaration "c3" (ErgoTypeConcept None (("a", ErgoTypeBoolean)::("b",ErgoTypeString)::nil)).
    
    Definition ergo_type2 :=
      mkErgoTypeModule
        "n2" nil (ergo_typed3::nil).

    Definition pkgs := ergo_type2 :: ergo_type1 :: nil.

    Definition tbls := names_tables_of_ergo_type_modules pkgs.
    (* Eval vm_compute in tbls. *)
    Definition res := elift (@List.concat _) (emaplift (resolve_names_in_module tbls) pkgs).
    (* Eval vm_compute in res. *)
  End Examples.
    
End ErgoType.
