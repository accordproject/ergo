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

open ErgoComp.ErgoCompiler
open ParseUtil

let welcome () =
  if Unix.isatty Unix.stdin
  then print_string ("Welcome to ERGOTOP version " ^ (Util.string_of_char_list ergo_version) ^ "\n")
  else ()

let ps1 = "ergo$ "
let ps2 = "  ... "

let prompt (ps : string) =
  if Unix.isatty Unix.stdin then
    print_string ps
  else ()

let rec read_chunk (first : bool) =
  prompt (if first then ps1 else ps2) ;
  let line = read_line () in
  if line = "" then
    read_chunk false
  else if String.get line ((String.length line) - 1) = '\\' then
    (String.sub line 0 ((String.length line) - 1)) ^ "\n" ^ (read_chunk false)
  else
    line ^ "\n"

let rec read_nonempty_multiline () = read_chunk true

(* Initialize the REPL ctxt, catching errors in input CTOs and modules *)
let safe_init_repl_ctxt ctos modules =
  ErgoUtil.wrap_jerrors
    (fun x -> x)
    (init_repl_context ctos modules)

(* REPL *)
let rec repl rctxt =
  (* read *)
  let text = read_nonempty_multiline () in
  try
    let rctxt' =
      begin match ParseUtil.parse_ergo_declaration_from_string "stdin" text with
      | Some decl ->
          begin
            (* eval *)
            let (out,rctxt') = ergo_repl_eval_decl rctxt decl in
            (* print *)
            print_string (ErgoUtil.wrap_jerrors Util.string_of_char_list out);
            rctxt'
          end
      | None -> rctxt
      end
    in
    (* loop *)
    repl rctxt'
  with
  | ErgoUtil.Ergo_Error e ->
      print_string (ErgoUtil.string_of_error_plus e text);
      print_string "\n" ;
      repl rctxt
  | End_of_file -> None

let args_list gconf =
  Arg.align
    [
      ("-version", Arg.Unit (ErgoUtil.get_version "The Ergo toplevel"),
       " Print version and exit");
      ("--version", Arg.Unit (ErgoUtil.get_version "The Ergo toplevel"),
       " Print version and exit");
    ]

let usage =
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

let main args =
  let gconf = ErgoConfig.default_config () in
  let (cto_files,input_files) = ErgoUtil.parse_args args_list usage args gconf in
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  List.iter (ErgoUtil.process_file (ErgoConfig.add_module_file gconf)) input_files;
  let ctos = ErgoConfig.get_ctos gconf in
  let modules = ErgoConfig.get_modules gconf in
  let rctxt = safe_init_repl_ctxt ctos modules in
  welcome ();
  repl rctxt

let wrap_error e =
  begin match e with
  | ErgoUtil.Ergo_Error error ->
      Printf.eprintf "%s\n" (ErgoUtil.string_of_error error); exit 2
  | exn ->
      Printf.eprintf "%s\n" (ErgoUtil.string_of_error (ErgoUtil.ergo_system_error (Printexc.to_string exn))); exit 2
  end

let _ =
    main (ErgoUtil.patch_argv Sys.argv)
