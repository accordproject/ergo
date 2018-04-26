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
      ("--target", Arg.String (ErgoConfig.set_target_lang gconf),
       "<lang> Indicates the language for the target (default: javascript)");
      ("--with-dispatch", Arg.Unit (ErgoConfig.set_with_dispatch_true gconf),
       " Generate dispatch function (default: false)")
    ]

let anon_args gconf cto_files input_files f =
  let extension = Filename.extension f in
  if extension = ".ctoj"
  then cto_files := (f, Util.string_of_file f) :: !cto_files
  else if extension = ".ergo"
  then input_files := f :: !input_files
  else raise (Ergo_Error (f ^ " is neither ctoj nor ergo file"))

let usage =
  "Ergo Compiler\n"^
  "Usage: "^Sys.argv.(0)^" [options] contract1 contract2 ..."

let parse_args gconf =
  let input_files = ref [] in
  let cto_files = ref [] in
  Arg.parse (args_list gconf) (anon_args gconf cto_files input_files) usage;
  (List.rev !cto_files, List.rev !input_files)

let () =
  let gconf = ErgoConfig.default_config () in
  let (cto_files,input_files) = parse_args gconf in
  batch_compile_top gconf cto_files input_files

