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
open Cto_j
open ErgoComp

let enum_case_of_decl d =
  char_list_of_string d.cto_decl_content_id.cto_id_name
    
let cto_enum_of_decls dl =
  List.map enum_case_of_decl dl

let base_type_of_decl d =
  begin match d with
  | None -> raise (Ergo_Error "Missing propertyType in CTO")
  | Some d ->
      begin match d.cto_prop_type_name with
      | "Bool" -> CTOBoolean
      | "String" -> CTOString
      | "Double" -> CTODouble
      | "Long" -> CTOLong
      | s -> CTOClassRef (ErgoCompiler.mk_class_ref None (char_list_of_string s))
      end
  end

let concept_field_of_decl d =
  let field_name = char_list_of_string d.cto_decl_content_id.cto_id_name in
  let base_type =
    base_type_of_decl d.cto_decl_content_propertyType
  in
  let field_type = base_type in
  let field_type =
    begin match d.cto_decl_content_array with
    | Some "[]" -> CTOArray field_type
    | Some _ -> raise (Ergo_Error "Mal-formed array option in CTO JSON representation")
    | None -> field_type
    end
  in
  let field_type =
    begin match d.cto_decl_content_optional with
    | None -> field_type
    | Some opt ->
	CTOOption (CTOArray base_type)
    end
  in
  (field_name, field_type)

let cto_concept_of_decls dl =
  List.map concept_field_of_decl dl

let cto_declaration_of_defn d =
  let decl_class = d.cto_defn_id.cto_id_name in
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
    | other ->
	raise (Ergo_Error ("Can't import CTO kind: " ^ other))
    end
  in
  { cto_declaration_class = ErgoCompiler.mk_class_ref None (char_list_of_string decl_class);
    cto_declaration_type = decl_type; }

let cto_declarations_of_body dl =
  List.map cto_declaration_of_defn dl

let cto_import (m:model) : cto_package =
  let namespace = char_list_of_string m.cto_namespace in
  let decls = cto_declarations_of_body m.cto_body in
  { cto_package_namespace = namespace;
    cto_package_declarations = decls; }

