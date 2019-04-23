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
open ErgoUtil
open ErgoConfig

let welcome () =
  if Unix.isatty Unix.stdin
  then print_string ("Welcome to ERGOTOP version " ^ ergo_version ^ "\n")
  else ()

let fmt_esc = "\x1b"
let fmt_csi = fmt_esc ^ "["

let fmt_red s = fmt_csi ^ "31m" ^ s ^ fmt_csi ^ "0m"
let fmt_grn s = fmt_csi ^ "32m" ^ s ^ fmt_csi ^ "0m"
let fmt_yel s = fmt_csi ^ "33m" ^ s ^ fmt_csi ^ "0m"
let fmt_blu s = fmt_csi ^ "34m" ^ s ^ fmt_csi ^ "0m"
let fmt_mag s = fmt_csi ^ "35m" ^ s ^ fmt_csi ^ "0m"

let fmt_out s =
  (Re.Str.global_replace (Re.Str.regexp "^Emit\\.") (fmt_mag "Emit.")
  (Re.Str.global_replace (Re.Str.regexp "^Response\\.") (fmt_grn "Response.")
  (Re.Str.global_replace (Re.Str.regexp "^State\\.") (fmt_blu "State.")
  (Re.Str.global_replace (Re.Str.regexp "^Failure\\.") (fmt_red "Failure.")
  s))))

let ps1 = fmt_yel "ergo$ "
let ps2 = fmt_yel "  ... "

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
let safe_init_repl_ctxt inputs =
  wrap_jerrors
    (fun x y -> x)
    (ErgoTopUtil.my_init_repl_context inputs)

(* REPL *)
let rec repl gconf rctxt =
  (* read *)
  let text = read_nonempty_multiline () in
  try
    let rctxt' =
      let decls = ParseUtil.parse_ergo_declarations_from_string "stdin" text in
      List.fold_left
        (fun rctxt decl ->
           begin
             (* eval *)
             let (out,rctxt') = ErgoTopUtil.my_ergo_repl_eval_decl rctxt decl in
             (* print *)
             print_string (fmt_out (wrap_jerrors (return_result_print_warnings gconf.econf_warnings text) out));
             rctxt'
           end)
        rctxt decls
    in
    (* loop *)
    repl gconf rctxt'
  with
  | Ergo_Error e ->
      print_string (string_of_error_with_source_text text e);
      print_string "\n" ;
      repl gconf rctxt
  | End_of_file -> None

let args_list gconf =
  Arg.align
    [
      ("-version", Arg.Unit (get_version "The Ergo toplevel"),
       " Print version and exit");
      ("--warnings", Arg.Unit (ErgoConfig.set_warnings gconf),
       " Print warnings");
    ]

let usage =
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

let main gconf args =
  let (cto_files,input_files,template_file) = parse_args args_list usage args gconf in
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  List.iter (ErgoConfig.add_module_file gconf) input_files;
  begin match template_file with
  | None -> ()
  | Some t -> ErgoConfig.add_template_file gconf t
  end;
  let all_modules = ErgoConfig.get_all_sorted gconf in
  let rctxt = safe_init_repl_ctxt all_modules in
  welcome ();
  repl gconf rctxt

let wrap_error gconf e =
  let source_table = ErgoConfig.get_source_table gconf in
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
  let gconf = ErgoConfig.default_config () in
  begin try
    main gconf (patch_argv Sys.argv)
  with
  | e ->
      wrap_error gconf e
  end
