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

open ErgoComp

let ergo_version = Util.string_of_char_list ergo_version

let get_version () =
  print_endline ("Ergo compiler version " ^ ergo_version);
  exit 0

let cto_import_decl_of_import_namespace ns =
  begin match String.rindex_opt ns '.' with
  | None ->
      raise (Util.Ergo_Error ("Malformed import: '" ^ ns ^ "' (should have at least one '.')"))
  | Some i ->
      let namespace = Util.char_list_of_string (String.sub ns 0 i) in
      let criteria_str = String.sub ns (i+1) (String.length ns - (i+1)) in
      let criteria =
        begin match criteria_str with
        | "*" -> ImportAll
        | _ -> ImportName (Util.char_list_of_string criteria_str)
        end
      in
      (namespace, criteria)
  end

let import_namespace_of_cto_import_decl i =
  let namespace_str = Util.string_of_char_list (fst i) in
  let criteria_str =
    begin match snd i with
    | ImportAll -> "*"
    | ImportName n -> Util.string_of_char_list n
    end
  in
  namespace_str ^ "." ^ criteria_str

