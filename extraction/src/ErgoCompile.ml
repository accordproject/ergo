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

type result_file = {
  res_file : string;
  res_content : string;
}

let compile_package_to_javascript ctos ergo =
  let code = ErgoCompiler.ergo_package_to_javascript ctos ergo in
  wrap_jerrors string_of_char_list code

let compile_package_to_javascript_cicero ctos ergo =
  let code = ErgoCompiler.ergo_package_to_javascript_cicero ctos ergo in
  wrap_jerrors string_of_char_list code

let compile_package_to_java ctos ergo =
  let code = ErgoCompiler.ergo_package_to_java ctos ergo in
  wrap_jerrors string_of_char_list code

let compile_inner target ctos file_content =
  let ergo_parsed = ParseString.parse_ergo_from_string file_content in
  begin match target with
  | Ergo -> ergo_raise (ergo_system_error "Target language cannot be Ergo")
  | JavaScript ->
      compile_package_to_javascript ctos ergo_parsed
  | JavaScriptCicero ->
      compile_package_to_javascript_cicero ctos ergo_parsed
  | Java ->
      compile_package_to_java ctos ergo_parsed
  end

let make_result_file target_lang source_file s =
  let fpref = Filename.chop_extension source_file in
  let ext = extension_of_lang target_lang in
  let fout = outname (target_f None fpref) ext in
  { res_file = fout;
    res_content = s; }

let ergo_compile gconf file_content =
  let target_lang = ErgoConfig.get_target_lang gconf in
  let ctos = ErgoConfig.get_ctos gconf in
  compile_inner target_lang ctos file_content

let ergo_proc gconf (file_name,file_content) =
  let target_lang = ErgoConfig.get_target_lang gconf in
  let result = ergo_compile gconf file_content in
  make_result_file target_lang file_name result

let batch_compile_top gconf cto_files input_files =
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  let results =
    List.map (process_file (ergo_proc gconf)) input_files
  in
  let output_res file_res =
    if file_res.res_file <> "" then
      begin
        Format.printf " compiled to: %s\n" file_res.res_file;
        make_file file_res.res_file file_res.res_content
      end
  in
  List.iter output_res results

