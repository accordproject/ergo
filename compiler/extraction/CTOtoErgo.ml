open Ast
open CTO
open Datatypes
open Ergo
open ErgoType
open List0
open Provenance

(** val cto_type_to_ergo_type : lrcto_type -> lrergo_type **)

let rec cto_type_to_ergo_type = function
| CTOBoolean loc -> ErgoTypeBoolean loc
| CTOString loc -> ErgoTypeString loc
| CTODouble loc -> ErgoTypeDouble loc
| CTOLong loc -> ErgoTypeLong loc
| CTOInteger loc -> ErgoTypeInteger loc
| CTODateTime loc -> ErgoTypeDateTime loc
| CTOClassRef (loc, n) -> ErgoTypeClassRef (loc, n)
| CTOOption (loc, ct1) -> ErgoTypeOption (loc, (cto_type_to_ergo_type ct1))
| CTOArray (loc, ct1) -> ErgoTypeArray (loc, (cto_type_to_ergo_type ct1))

(** val cto_declaration_desc_to_ergo_type_declaration_desc :
    lrcto_declaration_desc -> lrergo_type_declaration_desc **)

let cto_declaration_desc_to_ergo_type_declaration_desc = function
| CTOEnum ls -> ErgoTypeEnum ls
| CTOTransaction (on, isabs, crec) ->
  ErgoTypeTransaction (on, isabs,
    (map (fun xy -> ((fst xy), (cto_type_to_ergo_type (snd xy)))) crec))
| CTOConcept (on, isabs, crec) ->
  ErgoTypeConcept (on, isabs,
    (map (fun xy -> ((fst xy), (cto_type_to_ergo_type (snd xy)))) crec))
| CTOEvent (on, isabs, crec) ->
  ErgoTypeEvent (on, isabs,
    (map (fun xy -> ((fst xy), (cto_type_to_ergo_type (snd xy)))) crec))
| CTOAsset (on, isabs, crec) ->
  ErgoTypeAsset (on, isabs,
    (map (fun xy -> ((fst xy), (cto_type_to_ergo_type (snd xy)))) crec))
| CTOParticipant (on, isabs, crec) ->
  ErgoTypeParticipant (on, isabs,
    (map (fun xy -> ((fst xy), (cto_type_to_ergo_type (snd xy)))) crec))

(** val cto_declaration_to_ergo_type_declaration :
    lrcto_declaration -> lrergo_type_declaration **)

let cto_declaration_to_ergo_type_declaration d =
  { type_declaration_annot = d.cto_declaration_annot; type_declaration_name =
    d.cto_declaration_name; type_declaration_type =
    (cto_declaration_desc_to_ergo_type_declaration_desc
      d.cto_declaration_type) }

(** val cto_declaration_to_ergo_declaration :
    lrcto_declaration -> lrergo_declaration **)

let cto_declaration_to_ergo_declaration d =
  DType (d.cto_declaration_annot,
    (cto_declaration_to_ergo_type_declaration d))

(** val cto_import_to_ergo_declaration :
    provenance import_decl -> lrergo_declaration **)

let cto_import_to_ergo_declaration d =
  DImport ((import_annot d), d)

(** val cto_package_to_ergo_module : lrcto_package -> lrergo_module **)

let cto_package_to_ergo_module p =
  { module_annot = p.cto_package_annot; module_file = p.cto_package_file;
    module_prefix = p.cto_package_prefix; module_namespace =
    p.cto_package_namespace; module_declarations =
    (app (map cto_import_to_ergo_declaration p.cto_package_imports)
      (map cto_declaration_to_ergo_declaration p.cto_package_declarations)) }
