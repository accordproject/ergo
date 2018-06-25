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

(** Ergo is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import List.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EImport.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoNameResolution.

  (** There are three phases to the name resolution in ErgoType files/modules:
- build a per-namespace table containing all the local names mapped to their namespace resolve names
- for a module, resolve imports using the per-namespace table to build a full namespace mapping for that module
- resolve the names within a given module using the full namespace mapping for that module *)
  
  (** Maps local names to absolute names for a given ErgoType module *)
  Definition name_table : Set := list (local_name * absolute_name).
  Definition namespace_name_table : Set := list (namespace_name * name_table).

  (** Maps namespaces to the names table for that namespace *)
  Record resolution_context :=
    mkResolutionContext {
        type_names : name_table;
        function_names : name_table;
      }.

  Definition name_entry_of_ergo_type_declaration (ns:namespace_name) (decl:ergo_type_declaration) : local_name * absolute_name :=
    let ln := decl.(type_declaration_name) in
    (ln, absolute_name_of_local_name ns ln).

  Definition names_table_of_ergo_type_module (ns:namespace_name) (pkg:ergo_type_module) : name_table :=
    map (name_entry_of_ergo_type_declaration ns) pkg.(type_module_declarations).

  (** Note: this merges tables when the same namespace is used in more than one ErgoType module *)
  Definition names_tables_of_ergo_type_modules (pkgs: list ergo_type_module) : namespace_name_table :=
    let init : namespace_name_table := nil in
    let proc_one (acc:namespace_name_table) (pkg:ergo_type_module) : namespace_name_table :=
        let ns := pkg.(type_module_namespace) in
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
             (loc:location)
             (ns:namespace_name)
             (ic:import_criteria)
             (tbl:name_table) : eresult name_table :=
    match ic with
    | ImportAll => esuccess tbl
    | ImportName n =>
      match lookup string_dec tbl n with
      | None => import_name_not_found loc ns n
      | Some t => esuccess ((n,t)::nil)
      end
    end.

  Definition apply_imports_to_names_tables
             (loc:location)
             (ns:namespace_name)
             (tbls:namespace_name_table)
             (imports:list import_decl) : eresult name_table :=
    let init : eresult name_table := esuccess nil in
    let proc_one (acc:eresult name_table) (import:import_decl) : eresult name_table :=
        match lookup string_dec tbls (fst import) with
        | Some t =>
          elift2 (fun x y => app x y)
                 acc
                 (apply_import_to_names loc ns (snd import) t)
        | None => import_not_found loc (fst import)
        end
    in
    fold_left proc_one imports init.

  (** Local name lookup *)
  Definition local_name_resolution (loc:location) (module_ns:namespace_name) (tbl:name_table) (nr:name_ref) : eresult absolute_name :=
    match nr with
    | RelativeRef None ln =>
      match lookup string_dec tbl ln with
      | None => resolve_name_not_found loc module_ns ln
      | Some an => esuccess an
      end
    | RelativeRef (Some ns) ln =>
      esuccess  (absolute_name_of_local_name ns ln)
    | AbsoluteRef an =>
      esuccess an
    end.

  (** This is the name resolution *)
  Fixpoint resolve_ergo_type_desc
           (loc:location)
           (module_ns:namespace_name)
           (tbl:name_table)
           (t:ergo_type_desc) : eresult ergo_type_desc :=
    match t with
    | ErgoTypeAny => esuccess ErgoTypeAny
    | ErgoTypeNone => esuccess ErgoTypeNone
    | ErgoTypeBoolean => esuccess ErgoTypeBoolean
    | ErgoTypeString => esuccess ErgoTypeString
    | ErgoTypeDouble => esuccess ErgoTypeDouble
    | ErgoTypeLong => esuccess ErgoTypeLong
    | ErgoTypeInteger => esuccess ErgoTypeInteger
    | ErgoTypeDateTime => esuccess ErgoTypeDateTime
    | ErgoTypeClassRef r => elift ErgoTypeClassRef (elift AbsoluteRef (local_name_resolution loc module_ns tbl r))
    | ErgoTypeOption t => elift ErgoTypeOption (resolve_ergo_type module_ns tbl t)
    | ErgoTypeRecord r =>
      let initial_map := map (fun xy => (fst xy, resolve_ergo_type module_ns tbl (snd xy))) r in
      let lifted_map := emaplift (fun xy => elift (fun t => (fst xy, t)) (snd xy)) initial_map in
      elift ErgoTypeRecord lifted_map
    | ErgoTypeArray t => elift ErgoTypeArray (resolve_ergo_type module_ns tbl t)
    | ErgoTypeSum t1 t2 => elift2 ErgoTypeSum (resolve_ergo_type module_ns tbl t1) (resolve_ergo_type module_ns tbl t2)
    end
  with resolve_ergo_type
         (module_ns:namespace_name)
         (tbl:name_table)
         (et:ergo_type) : eresult ergo_type :=
         elift
           (fun etd =>
              mk_type (type_loc et) etd)
           (resolve_ergo_type_desc (type_loc et) module_ns tbl (type_desc et)).
  
  Definition resolve_ergo_type_struct
             (ns:namespace_name)
             (tbl:name_table)
             (t:list (string * ergo_type)) : eresult (list (string * ergo_type)) :=
    emaplift (fun xy =>
                elift (fun t => (fst xy, t)) (resolve_ergo_type ns tbl (snd xy))) t.

  Definition resolve_extends_name
             (loc:location)
             (ns:string)
             (tbl:name_table)
             (en:option name_ref) : eresult (option name_ref) :=
    match en with
    | None => esuccess None
    | Some ln => elift Some (elift AbsoluteRef (local_name_resolution loc ns tbl ln))
    end.

  Definition resolve_ergo_type_signature
             (ns:namespace_name)
             (tbl:name_table)
             (sig:ergo_type_signature) :=
    let params_types := resolve_ergo_type_struct ns tbl (sig.(type_signature_params)) in
    let output_type := resolve_ergo_type ns tbl sig.(type_signature_output) in
    let throws_type :=
        match sig.(type_signature_throws) with
        | None => esuccess None
        | Some throw_ty =>
          elift Some (resolve_ergo_type ns tbl throw_ty)
        end
    in
    let emits_type :=
        match sig.(type_signature_emits) with
        | None => esuccess None
        | Some throw_ty =>
          elift Some (resolve_ergo_type ns tbl throw_ty)
        end
    in
    elift4 (mkErgoTypeSignature
              sig.(type_signature_name) sig.(type_signature_location))
           params_types
           output_type
           throws_type
           emits_type.

  Definition resolve_ergo_type_clauses
             (ns:namespace_name)
             (tbl:name_table)
             (cls:list (string * ergo_type_signature)) : eresult (list (string * ergo_type_signature)) :=
    emaplift (fun xy => elift (fun r => (fst xy, r))
                              (resolve_ergo_type_signature ns tbl (snd xy))) cls.

  Definition resolve_decl_desc
             (loc:location)
             (module_ns:namespace_name)
             (tbl:name_table)
             (k:ergo_type_declaration_desc) : eresult ergo_type_declaration_desc :=
    match k with
    | ErgoTypeEnum l => esuccess (ErgoTypeEnum l)
    | ErgoTypeTransaction extends_name ergo_type_struct =>
      elift2 ErgoTypeTransaction
             (resolve_extends_name loc module_ns tbl extends_name)
             (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
    | ErgoTypeConcept extends_name ergo_type_struct =>
      elift2 ErgoTypeConcept
             (resolve_extends_name loc module_ns tbl extends_name)
             (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
    | ErgoTypeEvent extends_name ergo_type_struct =>
      elift2 ErgoTypeEvent
             (resolve_extends_name loc module_ns tbl extends_name)
             (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
    | ErgoTypeAsset extends_name ergo_type_struct =>
      elift2 ErgoTypeAsset
             (resolve_extends_name loc module_ns tbl extends_name)
             (resolve_ergo_type_struct module_ns tbl ergo_type_struct)
    | ErgoTypeParticipant extends_name ergo_type_struct =>
      elift2 ErgoTypeParticipant
             (resolve_extends_name loc module_ns tbl extends_name)
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

  Definition resolve_declaration (module_ns:namespace_name) (tbl:name_table) (decl: ergo_type_declaration) : eresult ergo_type_declaration :=
    let name := absolute_name_of_local_name module_ns decl.(type_declaration_name) in
    let edecl_desc := resolve_decl_desc decl.(type_declaration_location) module_ns tbl decl.(type_declaration_type) in
    elift (fun k => mkErgoTypeDeclaration name decl.(type_declaration_location) k) edecl_desc.
  
  Definition resolve_declarations (module_ns:namespace_name) (tbl:name_table) (decls: list ergo_type_declaration)
    : eresult (list ergo_type_declaration) :=
    emaplift (resolve_declaration module_ns tbl) decls.

  Definition resolve_names_in_module
             (tbls:namespace_name_table)
             (pkg:ergo_type_module) : eresult (list ergo_type_declaration) :=
    (** Make sure to add current namespace to the list of imports - i.e., import self. *)
    let imports := app pkg.(type_module_imports)
                             (("org.hyperledger.composer.system"%string, ImportAll)
                                ::(pkg.(type_module_namespace),ImportAll)::nil) in
    let module_ns := pkg.(type_module_namespace) in
    let in_scope_names := apply_imports_to_names_tables pkg.(type_module_location) module_ns tbls imports in
    eolift (fun tbls => resolve_declarations
                          pkg.(type_module_namespace)
                                tbls
                                pkg.(type_module_declarations)) in_scope_names.

  (** Top level *)
  Definition ergo_type_resolved_tbl_for_module
             (pkgs:list ergo_type_module) : eresult (list ergo_type_declaration) :=
    let tbls := names_tables_of_ergo_type_modules pkgs in
    elift (@List.concat _) (emaplift (resolve_names_in_module tbls) pkgs).

  Section Examples.
    Local Open Scope string.
    Definition ergo_typed1 :=
      mkErgoTypeDeclaration
        "c1"
        dummy_location
        (ErgoTypeConcept
           None
           (("a", mk_type dummy_location ErgoTypeBoolean)
              ::("b", mk_type dummy_location (ErgoTypeClassRef (RelativeRef None "c3")))::nil)).
    
    Definition ergo_typed2 :=
      mkErgoTypeDeclaration
        "c2"
        dummy_location
        (ErgoTypeConcept
           None
           (("c", mk_type dummy_location ErgoTypeBoolean)
              ::("d", mk_type dummy_location (ErgoTypeClassRef (RelativeRef None "c1")))::nil)).
    

    Definition ergo_type1 :=
      mkErgoTypeModule
        "n1"
        dummy_location
        (("n2",ImportAll)::nil) (ergo_typed1::ergo_typed2::nil).
    
    Definition ergo_typed3 :=
      mkErgoTypeDeclaration
        "c3"
        dummy_location
        (ErgoTypeConcept
           None
           (("a", mk_type dummy_location ErgoTypeBoolean)
              ::("b", mk_type dummy_location ErgoTypeString)::nil)).

    Definition ergo_type2 :=
      mkErgoTypeModule
        "n2" dummy_location nil (ergo_typed3::nil).

    Definition pkgs := ergo_type2 :: ergo_type1 :: nil.

    Definition tbls := names_tables_of_ergo_type_modules pkgs.
    (* Eval vm_compute in tbls. *)
    Definition res := elift (@List.concat _) (emaplift (resolve_names_in_module tbls) pkgs).
    (* Eval vm_compute in res. *)
  End Examples.

End ErgoNameResolution.

