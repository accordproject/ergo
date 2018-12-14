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

let res_convert code =
  (* Printf.printf "NNRC Module: %s" (pretty_nnrc_module false 0 false (Jarray []) false code.res_nnrc); *)
  (string_of_char_list code.res_file, string_of_char_list code.res_content)

let compile_module_to_javascript version inputs =
  let code = ErgoCompiler.ergo_module_to_javascript version inputs in
  wrap_jerrors res_convert code

let compile_module_to_cicero inputs =
  let code = ErgoCompiler.ergo_module_to_cicero inputs in
  wrap_jerrors res_convert code

let compile_module_to_java inputs =
  let code = ErgoCompiler.ergo_module_to_java inputs in
  wrap_jerrors res_convert code

let ergo_compile target_lang inputs =
  let result =
    begin match target_lang with
    | Ergo -> ergo_raise (ergo_system_error "Target language cannot be Ergo")
    | ES5 ->
        compile_module_to_javascript ES5 inputs
    | ES6 ->
        compile_module_to_javascript ES6 inputs
    | Cicero ->
        compile_module_to_cicero inputs
    | Java ->
        compile_module_to_java inputs
    end
  in
  result

let ergo_link gconf result =
  if should_link gconf
  then
    result ^ Resources.ergo_runtime
  else
    result

let ergo_proc gconf inputs =
  let target_lang = ErgoConfig.get_target_lang gconf in
  let ext = extension_of_lang target_lang in
  let (source_file,result) = ergo_compile target_lang inputs in
  Printf.printf "Compiling Ergo '%s' -- " source_file;
  let fpref = Filename.chop_extension source_file in
  let fout = outname (target_f None fpref) ext in
  let result = ergo_link gconf result in
  Printf.printf "creating '%s'\n" fout;
  make_file fout result

