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

open ErgoUtil
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
      ("--version", Arg.Unit ErgoUtil.get_version,
       " Prints the compiler version");
      ("--target", Arg.String (ErgoConfig.set_target_lang gconf),
       "<lang> Indicates the language for the target (default: javascript) " ^ available_targets)
    ]

let anon_args gconf cto_files input_files f =
  let extension = Filename.extension f in
  if extension = ".ctoj"
  then cto_files := (f, Util.string_of_file f) :: !cto_files
  else if extension = ".ergo"
  then input_files := f :: !input_files
  else ergo_raise (ergo_system_error (f ^ " is not cto, ctoj or ergo file"))

let usage =
  "Ergo Compiler\n"^
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

let parse fa args l f msg =
  try
    Arg.parse_argv (fa args) l f msg
  with
  | Arg.Bad msg -> Printf.eprintf "%s" msg; exit 2
  | Arg.Help msg -> Printf.printf "%s" msg; exit 0

let parse_args fa args gconf =
  let input_files = ref [] in
  let cto_files = ref [] in
  parse fa args (args_list gconf) (anon_args gconf cto_files input_files) usage;
  (List.rev !cto_files, List.rev !input_files)

let main fa args =
  let gconf = ErgoConfig.default_config () in
  let (cto_files,input_files) = parse_args fa args gconf in
  batch_compile_top gconf cto_files input_files

