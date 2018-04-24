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
open ErgoConfig

type result_file = {
  res_file : string;
  res_content : string;
}

let wrap_jerrors f e =
  begin match e with
  | Failure (CompilationError cl) ->
      raise (Ergo_Error ("[Compilation Error] " ^ (Util.string_of_char_list cl)))
  | Failure (TypeError cl) ->
      raise (Ergo_Error ("[Type Error] " ^ (Util.string_of_char_list cl)))
  | Failure (UserError d) ->
      let cl = ErgoCompiler.Data.data_to_json_string [] d in
      raise (Ergo_Error ("[User Error] " ^ (Util.string_of_char_list cl)))
  | Success x -> f x
  end

let parse_ergo file_content =
  ParseString.parse_ergo_from_string file_content
let parse_ergoc file_content =
  ParseString.parse_ergoc_sexp_from_string file_content

let compile_ergo_to_javascript ctos coname clname ergo =
  let coname = Util.char_list_of_string coname in
  let clname = Util.char_list_of_string clname in
  let code = ErgoCompiler.clause_code_from_ergo_package ctos coname clname ergo in
  wrap_jerrors Util.string_of_char_list code

let compile_ergo_to_calculus ctos ergo =
  let cal = ErgoCompiler.ergo_calculus_package_from_ergo_package ctos ergo in
  wrap_jerrors (fun cal -> SExp.sexp_to_string (AstsToSExp.ergoc_package_to_sexp cal)) cal

let compile_calculus_to_javascript coname clname ergoc =
  let coname = Util.char_list_of_string coname in
  let clname = Util.char_list_of_string clname in
  let code = ErgoCompiler.clause_code_from_ergoc_package coname clname ergoc in
  wrap_jerrors Util.string_of_char_list code

let compile_package_calculus_to_javascript ergoc =
  Util.string_of_char_list
    (ErgoCompiler.javascript_from_ergoc_package ergoc)

let compile_package_to_javascript ctos ergo =
  let code = ErgoCompiler.javascript_from_ergo_package ctos ergo in
  wrap_jerrors Util.string_of_char_list code

let compile_package_to_javascript_with_dispatch ctos coname ergo =
  let code = ErgoCompiler.javascript_from_ergo_package_with_dispatch ctos coname ergo in
  wrap_jerrors Util.string_of_char_list code

let force_contract_clause_names coname clname =
  begin match coname, clname with
  | Some coname, Some clname -> (coname, clname)
  | _ -> raise (Ergo_Error "JavaScript target currently requires a contract name and a clause name")
  end

let compile source target coname clname with_dispatch ctos file_content =
  begin match source,target with
  | _,Ergo -> raise (Ergo_Error "Target language cannot be Ergo")
  | JavaScript,_ -> raise (Ergo_Error "Source language cannot be JavaScript")
  | Calculus,Calculus -> raise (Ergo_Error "Source and target language have to be different")
  | Ergo,JavaScript ->
      let ergo_parsed = parse_ergo file_content in
      begin match coname,clname with
      | Some coname, Some clname ->
          compile_ergo_to_javascript ctos coname clname ergo_parsed
      | None, Some _ | Some _, None | None, None ->
          if with_dispatch
          then
            begin match coname with
            | None ->
                compile_package_to_javascript_with_dispatch
                  ctos None ergo_parsed
            | Some coname ->		  
                compile_package_to_javascript_with_dispatch
                  ctos (Some (Util.char_list_of_string coname)) ergo_parsed
            end
          else
            compile_package_to_javascript ctos ergo_parsed
      end
  | Ergo,Calculus ->
      let ergo_parsed = parse_ergo file_content in
      compile_ergo_to_calculus ctos ergo_parsed
  | Calculus,JavaScript ->
      let ergoc_parsed = parse_ergoc file_content in
      begin match coname,clname with
      | Some coname, Some clname ->
          compile_calculus_to_javascript coname clname ergoc_parsed
      | None, Some _ | Some _, None | None, None ->
          compile_package_calculus_to_javascript ergoc_parsed
      end
  end

let make_result_file target_lang source_file s =
  let fpref = Filename.chop_extension source_file in
  let ext = extension_of_lang target_lang in
  let fout = outname (target_f None fpref) ext in
  { res_file = fout;
    res_content = s; }

let ergo_compile gconf file_content =
  let source_lang = ErgoConfig.get_source_lang gconf in
  let target_lang = ErgoConfig.get_target_lang gconf in
  let contract_name = ErgoConfig.get_contract_name gconf in
  let clause_name = ErgoConfig.get_clause_name gconf in
  let with_dispatch = ErgoConfig.get_with_dispatch gconf in
  let ctos = ErgoConfig.get_ctos gconf in
  compile source_lang target_lang contract_name clause_name with_dispatch ctos file_content

let ergo_proc gconf (file_name,file_content) =
  let target_lang = ErgoConfig.get_target_lang gconf in
  let result = ergo_compile gconf file_content in
  make_result_file target_lang file_name result

