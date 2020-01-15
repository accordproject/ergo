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

open Ergo_lib
open Ergo_util

(* Command line args *)

let args_list gconf =
  Arg.align
    [
      ("-version", Arg.Unit (get_version "The Ergo compiler"),
       " Print version and exit");
      ("--version", Arg.Unit (get_version "The Ergo compiler"),
       " Print version and exit");
    ]

let usage =
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

let label_of_dependency ff dep =
  Format.fprintf ff " %s" dep

let label_of_dependencies ff deps =
  List.iter (label_of_dependency ff) deps

let print_dependency (x,ys) =
  Format.printf "%s:%a@\n" x label_of_dependencies ys

let main gconf args =
  let (cto_files,input_files,template_file) = parse_args args_list usage args gconf in
  List.iter (Config.add_cto_file gconf) cto_files;
  List.iter (Config.add_module_file gconf) input_files;
  begin match template_file with
  | None -> ()
  | Some t -> Config.add_template_file gconf t
  end;
  let all_modules = Config.get_all_sorted gconf in
  List.iter print_dependency (labels_of_graph all_modules)

let wrap_error gconf e =
  let source_table = Config.get_source_table gconf in
  begin match e with
  | Ergo_Error error ->
      Printf.eprintf "%s\n"
        (string_of_error_with_table source_table error);
      exit 2
  | exn ->
      Printf.eprintf "%s\n"
        (string_of_error_with_table source_table
           (ergo_system_error (Printexc.to_string exn)));
      exit 2
  end

let _ =
  let gconf = Config.default_config () in
  begin try
    main gconf (patch_argv Sys.argv)
  with
  | e ->
      wrap_error gconf e
  end

