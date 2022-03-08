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

let enum_case_of_property d =
  char_list_of_string d.cto_property_name

let cto_enum_of_properties dl =
  List.map enum_case_of_property dl

let mk_abstract j =
  begin match j with
  | Some true -> true
  | Some false
  | None -> false
  end

let mk_superType j =
  begin match j with
  | None -> None
  | Some ce -> Some (None, Util.char_list_of_string ce.cto_type_identifier_name)
  end

let mk_prov loc =
  begin match loc with
  | Some loc ->
      ErgoCompiler.prov_loc
        { loc_file = Util.char_list_of_string !filename;
          loc_start =
            { offset = loc.cto_range_start.cto_position_offset;
              line = loc.cto_range_start.cto_position_line;
              column = loc.cto_range_start.cto_position_column; };
          loc_end =
            { offset = loc.cto_range_end.cto_position_offset;
              line = loc.cto_range_end.cto_position_line;
              column = loc.cto_range_end.cto_position_column; }; }
  | None ->
      dummy_provenance
  end

let base_type_of_property loc d =
  begin match d.cto_property_ttype with
  | "concerto.metamodel.BooleanProperty" -> ErgoCompiler.cto_boolean loc
  | "concerto.metamodel.StringProperty" -> ErgoCompiler.cto_string loc
  | "concerto.metamodel.DoubleProperty" -> ErgoCompiler.cto_double loc
  | "concerto.metamodel.IntegerProperty" -> ErgoCompiler.cto_integer loc
  | "concerto.metamodel.LongProperty" -> ErgoCompiler.cto_long loc
  | "concerto.metamodel.DateTimeProperty" -> ErgoCompiler.cto_dateTime loc
  | s -> begin match d.cto_property_ptype with
         | None ->
            ergo_raise (ergo_system_error ("Mal-formed property, without a corresponding type identifier (class: " ^ s ^ ")"))
         | Some t ->
            ErgoCompiler.cto_class_ref loc
              (None,(char_list_of_string t.cto_type_identifier_name))
         end
  end

let field_of_property d =
  let loc = mk_prov d.cto_property_location in
  let field_name = char_list_of_string d.cto_property_name in
  let base_type =
    base_type_of_property loc d
  in
  let field_type = base_type in
  let field_type =
    begin match d.cto_property_isArray with
    | Some true -> ErgoCompiler.cto_array loc field_type
    | Some false
    | None -> field_type
    end
  in
  let field_type =
    begin match d.cto_property_isOptional with
    | Some true -> ErgoCompiler.cto_option loc field_type
    | Some false
    | None -> field_type
    end
  in
  (field_name, field_type)

let cto_fields_of_properties dl =
  List.map field_of_property dl

let cto_declaration_of_declaration d =
  let decl_class = d.cto_declaration_name in
  let loc = mk_prov d.cto_declaration_location in
  let abstract = mk_abstract d.cto_declaration_isAbstract in
  let extends = mk_superType d.cto_declaration_superType in
  let decl_type = 
    begin match d.cto_declaration_ttype with
    | "concerto.metamodel.EnumDeclaration" ->
        CTOEnum (cto_enum_of_properties d.cto_declaration_properties)
    | "concerto.metamodel.ConceptDeclaration" ->
        CTOConcept (abstract, extends, cto_fields_of_properties d.cto_declaration_properties)
    | "concerto.metamodel.TransactionDeclaration" ->
        CTOTransaction (abstract, extends, cto_fields_of_properties d.cto_declaration_properties)
    | "concerto.metamodel.EventDeclaration" ->
        CTOEvent (abstract, extends, cto_fields_of_properties d.cto_declaration_properties)
    | "concerto.metamodel.AssetDeclaration" ->
        CTOAsset (abstract, extends, cto_fields_of_properties d.cto_declaration_properties)
    | "concerto.metamodel.ParticipantDeclaration" ->
        CTOParticipant (abstract, extends, cto_fields_of_properties d.cto_declaration_properties)
    | other ->
        ergo_raise (ergo_system_error ("Can't import CTO kind: " ^ other))
    end
  in
  { cto_declaration_name = char_list_of_string decl_class;
    cto_declaration_annot = loc;
    cto_declaration_type = decl_type; }

let cto_declarations_of_declarations dl =
  List.map cto_declaration_of_declaration dl

let cto_import_decl_of_import ns =
  let loc = dummy_provenance in (* XXX Not in JSON *)
  let namespace = char_list_of_string ns.cto_import_namespace in
  begin match ns.cto_import_name with
  | None ->
     ImportAll (loc, namespace)
  | Some name ->
     ImportName (loc, namespace, char_list_of_string name)
  end

let cto_import f (m:model) : ErgoCompiler.cto_package =
  filename := f;
  let namespace = char_list_of_string m.cto_model_namespace in
  let imports = List.map cto_import_decl_of_import m.cto_model_imports in
  let decls = cto_declarations_of_declarations m.cto_model_declarations in
  { cto_package_namespace = namespace;
    cto_package_file = Util.char_list_of_string !filename;
    cto_package_prefix = Util.char_list_of_string (Util.class_prefix_of_filename !filename);
    cto_package_annot = dummy_provenance; (* XXX Not in JSON *)
    cto_package_imports = imports;
    cto_package_declarations = decls; }
