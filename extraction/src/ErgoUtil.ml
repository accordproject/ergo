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
open ErgoComp

(* Ergo Exception *)

exception Ergo_Error of eerror
let ergo_system_error msg =
  SystemError (char_list_of_string msg)
let ergo_parse_error msg =
  ParseError (char_list_of_string msg)
let ergo_compilation_error msg =
  CompilationError (char_list_of_string msg)
let ergo_type_error msg =
  TypeError (char_list_of_string msg)
let ergo_runtime_error msg =
  RuntimeError (char_list_of_string msg)

let ergo_raise error =
  raise (Ergo_Error error)

let error_kind error =
  begin match error with
  | SystemError _ -> "SystemError"
  | ParseError _ -> "ParseError"
  | CompilationError _ -> "CompilationError"
  | TypeError _ -> "TypeError"
  | RuntimeError _ -> "RuntimeError"
  end

let error_message error =
  let msg = 
    begin match error with
    | SystemError msg -> msg
    | ParseError msg -> msg
    | CompilationError msg -> msg
    | TypeError msg -> msg
    | RuntimeError msg -> msg
    end
  in string_of_char_list msg

(* Version number *)
let ergo_version = string_of_char_list ergo_version

let get_version () =
  print_endline ("Ergo compiler version " ^ ergo_version);
  exit 0

let cto_import_decl_of_import_namespace ns =
  begin match String.rindex_opt ns '.' with
  | None ->
      ergo_raise (ergo_parse_error ("Malformed import: '" ^ ns ^ "' (should have at least one '.')"))
  | Some i ->
      let namespace = char_list_of_string (String.sub ns 0 i) in
      let criteria_str = String.sub ns (i+1) (String.length ns - (i+1)) in
      let criteria =
        begin match criteria_str with
        | "*" -> ImportAll
        | _ -> ImportName (char_list_of_string criteria_str)
        end
      in
      (namespace, criteria)
  end

(** Additional utility functions *)

let process_file f file_name =
  Format.printf "Processing file: %s --" file_name;
  let file_content = string_of_file file_name in
  f (file_name,file_content)

let wrap_jerrors f e =
  begin match e with
  | Failure e -> ergo_raise e
  | Success x -> f x
  end

