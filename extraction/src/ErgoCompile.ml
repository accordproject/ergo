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

open PrettyIL

let res_convert code warnings =
  let contract_name =
    begin match code.res_contract_name with
    | None -> None
    | Some cn -> Some (string_of_char_list cn)
    end
  in
  (* Printf.printf "NNRC Module: %s" (pretty_nnrc_module false 0 false (Jarray []) false code.res_nnrc); *)
  (contract_name, string_of_char_list code.res_file, code.res_content, warnings)

let compile_module_to_javascript version inputs template =
  let code = ErgoCompiler.ergo_module_to_javascript version inputs template in
  wrap_jerrors res_convert code

let compile_module_to_cicero inputs template =
  let code = ErgoCompiler.ergo_module_to_cicero inputs template in
  wrap_jerrors res_convert code

let compile_module_to_java inputs template =
  let code = ErgoCompiler.ergo_module_to_java inputs template in
  wrap_jerrors res_convert code

let ergo_compile target_lang inputs template =
  let result =
    begin match target_lang with
    | Ergo -> ergo_raise (ergo_system_error "Target language cannot be Ergo")
    | ES5 ->
        compile_module_to_javascript ES5 inputs template
    | ES6 ->
        compile_module_to_javascript ES6 inputs template
    | Cicero ->
        compile_module_to_cicero inputs template
    | Java ->
        compile_module_to_java inputs template
    end
  in
  result

let ergo_link gconf result =
  if should_link gconf
  then
    result ^ Resources.ergo_runtime
  else
    result

let print_generate source_file ext result =
  let fpref = Filename.chop_extension source_file in
  let fout = outname (target_f None fpref) ext in
  Printf.printf " '%s'\n" fout;
  make_file fout result

let print_monitor source_file =
  if !Util.monitoring
  then
    let result = Util.get_monitor_output () in
    Printf.printf "Monitoring for '%s' -->" source_file;
    print_generate source_file ".monitor.json" result
  else ()

let ergo_proc gconf inputs =
  let target_lang = ErgoConfig.get_target_lang gconf in
  let source_table = ErgoConfig.get_source_table gconf in
  let ext = extension_of_lang target_lang in
  let template = ErgoConfig.get_template gconf in
  let (contract_name,source_file,result,warnings) = ergo_compile target_lang inputs template in
  Printf.printf "Compiling Ergo '%s' -- " source_file;
  let result = ergo_link gconf result in
  if gconf.econf_warnings then print_warnings_with_table source_table warnings;
  print_generate source_file ext result;
  print_monitor source_file
