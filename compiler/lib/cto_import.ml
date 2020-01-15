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

open Util
open Ergo_util
open Core
open Cto_j

let filename = ref ""

let enum_case_of_decl d =
  char_list_of_string d.cto_decl_content_id.cto_id_name

let cto_enum_of_decls dl =
  List.map enum_case_of_decl dl

let mk_abstract j =
  begin match j with
  | None -> false
  | Some _ -> true
  end

let mk_extends j =
  begin match j with
  | None -> None
  | Some ce -> Some (None, Util.char_list_of_string ce.cto_extends_class.cto_extends_name)
  end

let mk_prov loc =
  begin match loc with
  | Some loc ->
      ErgoCompiler.prov_loc
        { loc_file = Util.char_list_of_string !filename;
          loc_start =
            { offset = loc.cto_location_start.cto_loc_offset;
              line = loc.cto_location_start.cto_loc_line;
              column = loc.cto_location_start.cto_loc_column; };
          loc_end =
            { offset = loc.cto_location_end.cto_loc_offset;
              line = loc.cto_location_end.cto_loc_line;
              column = loc.cto_location_end.cto_loc_column; }; }
  | None ->
      dummy_provenance
  end

let base_type_of_decl loc d =
  begin match d with
  | None -> ergo_raise (ergo_system_error "Missing propertyType in CTO")
  | Some d ->
      begin match d.cto_prop_type_name with
      | "Boolean" -> ErgoCompiler.cto_boolean loc
      | "String" -> ErgoCompiler.cto_string loc
      | "Double" -> ErgoCompiler.cto_double loc
      | "Integer" -> ErgoCompiler.cto_integer loc
      | "Long" -> ErgoCompiler.cto_long loc
      | "DateTime" -> ErgoCompiler.cto_dateTime loc
      | s -> ErgoCompiler.cto_class_ref loc
               (None,(char_list_of_string s))
      end
  end

let field_of_decl d =
  let loc = mk_prov (Some d.cto_decl_content_location) in
  let field_name = char_list_of_string d.cto_decl_content_id.cto_id_name in
  let base_type =
    base_type_of_decl loc d.cto_decl_content_propertyType
  in
  let field_type = base_type in
  let field_type =
    begin match d.cto_decl_content_array with
    | Some "[]" -> ErgoCompiler.cto_array loc field_type
    | Some _ -> ergo_raise (ergo_system_error "Mal-formed array option in CTO JSON representation")
    | None -> field_type
    end
  in
  let field_type =
    begin match d.cto_decl_content_optional with
    | None -> field_type
    | Some opt ->
        ErgoCompiler.cto_option loc field_type
    end
  in
  (field_name, field_type)

let cto_concept_of_decls dl =
  List.map field_of_decl dl

let cto_event_of_decls dl =
  List.map field_of_decl dl

let cto_asset_of_decls dl =
  List.map field_of_decl dl

let cto_participant_of_decls dl =
  List.map field_of_decl dl

let cto_declaration_of_defn d =
  let decl_class = d.cto_defn_id.cto_id_name in
  let loc = mk_prov d.cto_defn_location in
  let abstract = mk_abstract d.cto_defn_abstract in
  let extends = mk_extends d.cto_defn_classExtension in
  (* if abstract then Printf.printf "Found abstract class: %s !\n" decl_class; *)
  (* if abstract then Printf.printf "Found abstract class: %s !\n" decl_class; *)
  let decl_type = 
    begin match d.cto_defn_ttype with
    | "EnumDeclaration" ->
        CTOEnum (cto_enum_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "TransactionDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOTransaction (abstract, extends, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "ConceptDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOConcept (abstract, extends, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "EventDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOEvent (abstract, extends, cto_event_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "AssetDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOAsset (abstract, extends, cto_asset_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "ParticipantDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOParticipant (abstract, extends, cto_participant_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | other ->
        ergo_raise (ergo_system_error ("Can't import CTO kind: " ^ other))
    end
  in
  { cto_declaration_name = char_list_of_string decl_class;
    cto_declaration_annot = loc;
    cto_declaration_type = decl_type; }

let cto_declarations_of_body dl =
  List.map cto_declaration_of_defn dl

let cto_import_of_import i =
  cto_import_decl_of_import_namespace i.cto_import_namespace

let cto_import f (m:model) : ErgoCompiler.cto_package =
  filename := f;
  let namespace = char_list_of_string m.cto_namespace in
  let imports = List.map cto_import_of_import m.cto_imports in
  let decls = cto_declarations_of_body m.cto_body in
  { cto_package_namespace = namespace;
    cto_package_file = Util.char_list_of_string !filename;
    cto_package_prefix = Util.char_list_of_string (Util.class_prefix_of_filename !filename);
    cto_package_annot = dummy_provenance; (* XXX Not in JSON *)
    cto_package_imports = imports;
    cto_package_declarations = decls; }

