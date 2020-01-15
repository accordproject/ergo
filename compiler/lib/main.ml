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

open Config

(* Command line args *)

let args_list gconf =
  Arg.align
    [
      ("--version", Arg.Unit (Ergo_util.get_version "The Ergo compiler"),
       " print version and exit");
      ("--target", Arg.String (set_target_lang gconf),
       "<lang> target platform (default: es6) " ^ available_targets_message);
      ("--link", Arg.Unit (set_link gconf),
       " link the Ergo runtime with the target code (es5,es6,cicero only)");
      ("--monitor", Arg.Set Util.monitoring,
       " produce compilation time information");
      ("--warnings", Arg.Unit (set_warnings gconf),
       " print warnings");
    ]

let usage =
  "Usage: "^Filename.basename (Sys.argv.(0))^" [options] [cto files] [ergo files]"

let main gconf args =
  let (cto_files,input_files,template_file) = Ergo_util.parse_args args_list usage args gconf in
  List.iter (add_cto_file gconf) cto_files;
  List.iter (add_module_file gconf) input_files;
  begin match template_file with
  | None -> ()
  | Some t -> add_template_file gconf t
  end;
  let all_modules = get_all_sorted gconf in
  Compile.ergo_proc gconf all_modules

