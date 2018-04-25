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
open ErgoCompile
open Cto_t

(* Command line args *)

let args_list gconf =
  Arg.align
    [
      ("-version", Arg.Unit ErgoUtil.get_version,
       " Prints the compiler version");
      ("--contractname", Arg.String (ErgoConfig.set_contract_name gconf),
       " <name> contract name");
      ("--clausename", Arg.String (ErgoConfig.set_clause_name gconf),
       " <name> clause name");
      ("--source", Arg.String (ErgoConfig.set_source_lang gconf),
       "<lang> Indicates the language for the source (default: ergo)");
      ("--target", Arg.String (ErgoConfig.set_target_lang gconf),
       "<lang> Indicates the language for the target (default: javascript)");
      ("--with-dispatch", Arg.Unit (ErgoConfig.set_with_dispatch_true gconf),
       " Generate dispatch function (default: false)")
    ]

let anon_args gconf input_files f =
  let extension = Filename.extension f in
  if extension = ".cto"
  then ErgoConfig.add_cto_file gconf f
  else if extension = ".ergo"
  then input_files := f :: !input_files
  else raise (Ergo_Error (f ^ " is neither cto nor ergo file"))

let usage =
  "Ergo Compiler\n"^
  "Usage: "^Sys.argv.(0)^" [options] contract1 contract2 ..."

let parse_args gconf =
  let input_files = ref [] in
  Arg.parse (args_list gconf) (anon_args gconf input_files) usage;
  List.rev !input_files

let () =
  let gconf = ErgoConfig.default_config () in
  let input_files = parse_args gconf in
  let results =
    List.map (Util.process_file (ergo_proc gconf)) input_files
  in
  let output_res file_res =
    if file_res.res_file <> "" then
      begin
        Format.printf " compiled to: %s\n" file_res.res_file;
        make_file file_res.res_file file_res.res_content
      end
  in
  List.iter output_res results

