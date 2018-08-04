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
      ("-version", Arg.Unit (ErgoUtil.get_version "The Ergo compiler"),
       " Print version and exit");
      ("--version", Arg.Unit (ErgoUtil.get_version "The Ergo compiler"),
       " Print version and exit");
      ("--target", Arg.String (ErgoConfig.set_target_lang gconf),
       "<lang> Indicates the language for the target (default: javascript) " ^ available_targets)
    ]

let usage =
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

let main gconf args =
  let (cto_files,input_files) = ErgoUtil.parse_args args_list usage args gconf in
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  List.iter (ErgoConfig.add_module_file gconf) input_files;
  let all_modules = ErgoConfig.get_all_sorted gconf in
  let (initmls, main) = get_last_ergo all_modules in
  begin match main with
  | Some main ->
      ErgoCompile.ergo_proc gconf initmls main
  | _ -> ()
  end

