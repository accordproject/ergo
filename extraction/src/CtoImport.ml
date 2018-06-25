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
open ErgoUtil
open ErgoComp
open Cto_j

let enum_case_of_decl d =
  char_list_of_string d.cto_decl_content_id.cto_id_name

let cto_enum_of_decls dl =
  List.map enum_case_of_decl dl

let mk_loc loc =
  begin match loc with
  | Some loc ->
      { loc_start =
          { offset = loc.cto_location_start.cto_loc_offset;
            line = loc.cto_location_start.cto_loc_line;
            column = loc.cto_location_start.cto_loc_column; };
        loc_end =
          { offset = loc.cto_location_end.cto_loc_offset;
            line = loc.cto_location_end.cto_loc_line;
            column = loc.cto_location_end.cto_loc_column; }; }
  | None ->
      dummy_location
  end

let base_type_of_decl d =
  begin match d with
  | None -> ergo_raise (ergo_system_error "Missing propertyType in CTO")
  | Some d ->
      begin match d.cto_prop_type_name with
      | "Boolean" -> ErgoCompiler.cto_boolean (mk_loc d.cto_prop_type_location)
      | "String" -> ErgoCompiler.cto_string (mk_loc d.cto_prop_type_location)
      | "Double" -> ErgoCompiler.cto_double (mk_loc d.cto_prop_type_location)
      | "Integer" -> ErgoCompiler.cto_integer (mk_loc d.cto_prop_type_location)
      | "Long" -> ErgoCompiler.cto_long (mk_loc d.cto_prop_type_location)
      | "DateTime" -> ErgoCompiler.cto_dateTime (mk_loc d.cto_prop_type_location)
      | s -> ErgoCompiler.cto_class_ref (mk_loc d.cto_prop_type_location)
               (RelativeRef (None,(char_list_of_string s)))
      end
  end

let field_of_decl d =
  let loc = mk_loc (Some d.cto_decl_content_location) in
  let field_name = char_list_of_string d.cto_decl_content_id.cto_id_name in
  let base_type =
    base_type_of_decl d.cto_decl_content_propertyType
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
        ErgoCompiler.cto_option loc (ErgoCompiler.cto_array loc base_type)
    end
  in
  (field_name, field_type)

let cto_concept_of_decls dl =
  List.map field_of_decl dl

let cto_event_of_decls dl =
  List.map field_of_decl dl

let cto_declaration_of_defn d =
  let decl_class = d.cto_defn_id.cto_id_name in
  let loc = mk_loc d.cto_defn_location in
  let decl_type = 
    begin match d.cto_defn_ttype with
    | "EnumDeclaration" ->
        CTOEnum (cto_enum_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "TransactionDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOTransaction (None, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "ConceptDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOConcept (None, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "EventDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOEvent (None, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "AssetDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOAsset (None, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | "ParticipantDeclaration" ->
        (* XXX First parameter is inheritance TBD *)
        CTOParticipant (None, cto_concept_of_decls d.cto_defn_body.cto_defn_content_declarations)
    | other ->
        ergo_raise (ergo_system_error ("Can't import CTO kind: " ^ other))
    end
  in
  { cto_declaration_name = char_list_of_string decl_class;
    cto_declaration_location = loc;
    cto_declaration_type = decl_type; }

let cto_declarations_of_body dl =
  List.map cto_declaration_of_defn dl

let cto_import_of_import i =
  ErgoUtil.cto_import_decl_of_import_namespace i.cto_import_namespace

let cto_import (m:model) : cto_package =
  let namespace = char_list_of_string m.cto_namespace in
  let imports = List.map cto_import_of_import m.cto_imports in
  let decls = cto_declarations_of_body m.cto_body in
  { cto_package_namespace = namespace;
    cto_package_location = dummy_location; (* XXX Not in JSON *)
    cto_package_imports = imports;
    cto_package_declarations = decls; }

