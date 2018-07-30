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
  ESystemError (dummy_provenance,char_list_of_string msg)
let ergo_parse_error msg start_pos end_pos =
  EParseError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_compilation_error msg start_pos end_pos =
  ECompilationError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_type_error msg start_pos end_pos =
  ETypeError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)
let ergo_runtime_error msg start_pos end_pos =
  ERuntimeError (mk_provenance_of_loc_pair start_pos end_pos, char_list_of_string msg)

let ergo_raise error =
  raise (Ergo_Error error)

let error_kind error =
  begin match error with
  | ESystemError (_,_) -> "SystemError"
  | EParseError (_,_) -> "ParseError"
  | ECompilationError (_,_) -> "CompilationError"
  | ETypeError (_,_) -> "TypeError"
  | ERuntimeError (_,_) -> "RuntimeError"
  end

let error_message error =
  let msg = 
    begin match error with
    | ESystemError (_,msg) -> msg
    | EParseError (_,msg) -> msg
    | ECompilationError (_,msg) -> msg
    | ETypeError (_,msg) -> msg
    | ERuntimeError (_,msg) -> msg
    end
  in string_of_char_list msg

let error_loc_start error =
  begin match error with
  | ESystemError (loc,_) -> (loc_of_provenance loc).loc_start
  | EParseError (prov,_) -> (loc_of_provenance prov).loc_start
  | ECompilationError (prov,_) -> (loc_of_provenance prov).loc_start
  | ETypeError (prov,_) -> (loc_of_provenance prov).loc_start
  | ERuntimeError (prov,_) -> (loc_of_provenance prov).loc_start
  end
let error_loc_end error =
  begin match error with
  | ESystemError (prov,_) -> (loc_of_provenance prov).loc_end
  | EParseError (prov,_) -> (loc_of_provenance prov).loc_end
  | ECompilationError (prov,_) -> (loc_of_provenance prov).loc_end
  | ETypeError (prov,_) -> (loc_of_provenance prov).loc_end
  | ERuntimeError (prov,_) -> (loc_of_provenance prov).loc_end
  end

let underline_prov prov text =
  begin try
    let loc = loc_of_provenance prov in
    let lines = String.split_on_char '\n' text in
    let line = List.nth lines (loc.loc_start.line - 1) in
    let underline =
      String.init
        (String.length line)
        (fun n ->
           if (n >= loc.loc_start.column && n < loc.loc_end.column)
           then '^'
           else ' ')
    in
    "\n" ^ line ^ "\n" ^ underline
  with
  | _ -> ""
  end

let string_of_error_prov prov =
  let loc = loc_of_provenance prov in
  "line " ^ (string_of_int loc.loc_start.line)
  ^ " col " ^ (string_of_int loc.loc_start.column)

let string_of_error error =
  begin match error with
  | ESystemError _ -> "[SystemError] " ^ (error_message error)
  | EParseError (prov, _) -> "[ParseError at " ^ (string_of_error_prov prov) ^ "] " ^ (error_message error)
  | ECompilationError (prov, _) -> "[CompilationError at " ^ (string_of_error_prov prov) ^ "] " ^  (error_message error)
  | ETypeError (prov, _) -> "[TypeError at " ^ (string_of_error_prov prov) ^ "] " ^ (error_message error)
  | ERuntimeError (prov, _) -> "[RuntimeError at " ^ (string_of_error_prov prov) ^ "] " ^  (error_message error)
  end

let string_of_error_plus error text =
  begin match error with
  | ESystemError _ -> "[SystemError] " ^ (error_message error)
  | EParseError (prov, _) -> "[ParseError at " ^ (string_of_error_prov prov) ^ "] " ^ (error_message error) ^ (underline_prov prov text)
  | ECompilationError (prov, _) -> "[CompilationError at " ^ (string_of_error_prov prov) ^ "] " ^  (error_message error) ^ (underline_prov prov text)
  | ETypeError (prov, _) -> "[TypeError at " ^ (string_of_error_prov prov) ^ "] " ^ (error_message error) ^ (underline_prov prov text)
  | ERuntimeError (prov, _) -> "[RuntimeError at " ^ (string_of_error_prov prov) ^ "] " ^  (error_message error) ^ (underline_prov prov text)
  end

(** Version number *)
let ergo_version = string_of_char_list ergo_version

let get_version cmd () =
  print_endline (cmd ^ ", version " ^ ergo_version);
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

(** Command line args *)
let patch_cto_extension f =
  begin try
    let extension = Filename.extension f in
    if extension = ".cto"
    then
      (Filename.chop_suffix f ".cto") ^ ".ctoj"
    else f
  with
  | _ -> f
  end

let patch_argv argv =
  Array.map patch_cto_extension argv

let anon_args gconf cto_files input_files f =
  let extension = Filename.extension f in
  if extension = ".ctoj"
  then cto_files := (f, Util.string_of_file f) :: !cto_files
  else if extension = ".ergo"
  then input_files := f :: !input_files
  else ergo_raise (ergo_system_error (f ^ " is not cto, ctoj or ergo file"))

let parse_args args_list usage args gconf =
  let parse args l f msg =
    try
      Arg.parse_argv args l f msg
    with
    | Arg.Bad msg -> Printf.eprintf "%s" msg; exit 2
    | Arg.Help msg -> Printf.printf "%s" msg; exit 0
  in
  let input_files = ref [] in
  let cto_files = ref [] in
  parse args (args_list gconf) (anon_args gconf cto_files input_files) usage;
  (List.rev !cto_files, List.rev !input_files)

