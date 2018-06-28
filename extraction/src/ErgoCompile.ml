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
open ErgoConfig

let compile_module_to_javascript ctos mls ergo =
  let code = ErgoCompiler.ergo_module_to_javascript ctos mls ergo in
  wrap_jerrors string_of_char_list code

let compile_module_to_javascript_cicero ctos mls ergo =
  let code = ErgoCompiler.ergo_module_to_javascript_cicero ctos mls ergo in
  wrap_jerrors string_of_char_list code

let compile_module_to_java ctos mls ergo =
  let code = ErgoCompiler.ergo_module_to_java ctos mls ergo in
  wrap_jerrors string_of_char_list code

let ergo_parse gconf (file_name,file_content) =
  ParseString.parse_ergo_from_string file_content

let ergo_compile gconf mls file_content =
  let target = ErgoConfig.get_target_lang gconf in
  let ctos = ErgoConfig.get_ctos gconf in
  let ergo_parsed = ParseString.parse_ergo_from_string file_content in
  let result =
    begin match target with
    | Ergo -> ergo_raise (ergo_system_error "Target language cannot be Ergo")
    | JavaScript ->
        compile_module_to_javascript ctos (List.rev !mls) ergo_parsed
    | JavaScriptCicero ->
        compile_module_to_javascript_cicero ctos (List.rev !mls) ergo_parsed
    | Java ->
        compile_module_to_java ctos (List.rev !mls) ergo_parsed
    end
  in
  mls := ergo_parsed :: !mls;
  result

let ergo_proc gconf mls (file_name,file_content) =
  Printf.printf "Processing file: %s --" file_name;
  let target_lang = ErgoConfig.get_target_lang gconf in
  let result = ergo_compile gconf mls file_content in
  let file_res = make_result_file (extension_of_lang target_lang) file_name result in
  if file_res.res_file <> "" then
    begin
      Printf.printf " compiled to: %s\n" file_res.res_file;
      make_file file_res.res_file file_res.res_content
    end

let get_stdlib gconf =
  List.map (process_file (ergo_parse gconf)) stdlibErgo

let batch_compile_top gconf cto_files input_files =
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  let mls = ref (get_stdlib gconf) in
  List.iter (process_file (ergo_proc gconf mls)) input_files
