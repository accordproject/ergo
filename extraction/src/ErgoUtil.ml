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

(** Ergo errors *)
exception Ergo_Error of eerror
let mk_position_point_of_loc pos =
  { offset = pos.Lexing.pos_cnum;
    line = pos.Lexing.pos_lnum;
    column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol; }
let mk_position_of_loc_pair start_pos end_pos =
  { loc_file = None; (* XXX TO BE FIXED *)
    loc_start = mk_position_point_of_loc start_pos;
    loc_end = mk_position_point_of_loc end_pos; }
let mk_provenance_of_loc_pair start_pos end_pos =
  ErgoCompiler.prov_loc (mk_position_of_loc_pair start_pos end_pos)
let ergo_system_error msg =
  SystemError (dummy_provenance,char_list_of_string msg)
let ergo_parse_error msg start_pos end_pos =
  ParseError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_compilation_error msg start_pos end_pos =
  CompilationError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_type_error msg start_pos end_pos =
  TypeError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_runtime_error msg start_pos end_pos =
  RuntimeError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)

let ergo_raise error =
  raise (Ergo_Error error)

let error_kind error =
  begin match error with
  | SystemError (_,_) -> "SystemError"
  | ParseError (_,_) -> "ParseError"
  | CompilationError (_,_) -> "CompilationError"
  | TypeError (_,_) -> "TypeError"
  | RuntimeError (_,_) -> "RuntimeError"
  end

let error_message error =
  let msg = 
    begin match error with
    | SystemError (_,msg) -> msg
    | ParseError (_,msg) -> msg
    | CompilationError (_,msg) -> msg
    | TypeError (_,msg) -> msg
    | RuntimeError (_,msg) -> msg
    end
  in string_of_char_list msg

let error_loc_start error =
  begin match error with
  | SystemError (loc,_) -> (loc_of_provenance loc).loc_start
  | ParseError (prov,_) -> (loc_of_provenance prov).loc_start
  | CompilationError (prov,_) -> (loc_of_provenance prov).loc_start
  | TypeError (prov,_) -> (loc_of_provenance prov).loc_start
  | RuntimeError (prov,_) -> (loc_of_provenance prov).loc_start
  end
let error_loc_end error =
  begin match error with
  | SystemError (prov,_) -> (loc_of_provenance prov).loc_end
  | ParseError (prov,_) -> (loc_of_provenance prov).loc_end
  | CompilationError (prov,_) -> (loc_of_provenance prov).loc_end
  | TypeError (prov,_) -> (loc_of_provenance prov).loc_end
  | RuntimeError (prov,_) -> (loc_of_provenance prov).loc_end
  end

let string_of_error_prov prov =
  let loc = loc_of_provenance prov in
  "line " ^ (string_of_int loc.loc_start.line)
  ^ " character " ^ (string_of_int loc.loc_start.column)

let string_of_error error =
  begin match error with
  | SystemError _ -> "[SystemError] " ^ (error_message error)
  | ParseError (prov, _) -> "[ParseError at " ^ (string_of_error_prov prov) ^ "] " ^ (error_message error)
  | CompilationError (prov, _) -> "[CompilationError at " ^ (string_of_error_prov prov) ^ "] " ^  (error_message error)
  | TypeError (prov, _) -> "[TypeError at " ^ (string_of_error_prov prov) ^ "]" ^ (error_message error)
  | RuntimeError (prov, _) -> "[RuntimeError at " ^ (string_of_error_prov prov) ^ "]" ^  (error_message error)
  end

(** Version number *)
let ergo_version = string_of_char_list ergo_version

let get_version () =
  print_endline ("Ergo compiler version " ^ ergo_version);
  exit 0

(** Additional utility functions *)
let process_file f file_name =
  let file_content = string_of_file file_name in
  f (file_name,file_content)

type result_file = {
  res_file : string;
  res_content : string;
}

let make_result_file ext source_file s =
  let fpref = Filename.chop_extension source_file in
  let fout = outname (target_f None fpref) ext in
  { res_file = fout;
    res_content = s; }

let wrap_jerrors f e =
  begin match e with
  | Failure e -> ergo_raise e
  | Success x -> f x
  end

(** Ergo call *)
let ergo_call contract_name =
  Util.string_of_char_list
    (ErgoCompiler.javascript_identifier_sanitizer (Util.char_list_of_string contract_name))

(** CTO import *)
let cto_import_decl_of_import_namespace ns =
  begin match String.rindex_opt ns '.' with
  | None ->
      ergo_raise (ergo_system_error ("Malformed import: '" ^ ns ^ "' (should have at least one '.')"))
  | Some i ->
      let namespace = char_list_of_string (String.sub ns 0 i) in
      let criteria_str = String.sub ns (i+1) (String.length ns - (i+1)) in
      begin match criteria_str with
      | "*" -> ImportAll (dummy_provenance, namespace)
      | _ -> ImportName (dummy_provenance,namespace,char_list_of_string criteria_str)
      end
  end

