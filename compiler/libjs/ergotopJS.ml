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

open Js_of_ocaml

open ParseUtil
open ErgoUtil
open ErgoConfig

let welcome () =
  print_string ("Welcome to ERGOTOP version " ^ ergo_version ^ "\n")

(* REPL *)

let repl gconf rctxt text =
  try
      let decls = ParseUtil.parse_ergo_declarations_from_string "stdin" text in
      List.fold_left
        (fun (answer,rctxt) decl ->
           begin
             (* eval *)
             let (out,rctxt') = ErgoTopUtil.my_ergo_repl_eval_decl rctxt decl in
             (* print *)
             (answer ^ (wrap_jerrors (return_result_print_warnings gconf.econf_warnings text) out), rctxt')
           end)
        ("",rctxt) decls
  with
    ErgoUtil.Ergo_Error e -> (ErgoUtil.string_of_error_with_source_text text e ^ "\n", rctxt)

let args_list gconf =
  Arg.align
    [
      ("-version", Arg.Unit (get_version "The Ergo toplevel"),
       " Print version and exit");
      ("--version", Arg.Unit (get_version "The Ergo toplevel"),
       " Print version and exit");
    ]

let usage =
  "Usage: "^Sys.argv.(0)^" [options] cto1 cto2 ... contract1 contract2 ..."

(* Initialize the REPL ctxt, catching errors in input CTOs and modules *)
let safe_init_repl_ctxt inputs =
  ErgoUtil.wrap_jerrors
    (fun x w -> x)
    (ErgoTopUtil.my_init_repl_context inputs)

let make_init_rctxt gconf =
  let all_modules = ErgoConfig.get_all_sorted gconf in
  let rctxt = safe_init_repl_ctxt all_modules in
  rctxt

let main gconf args =
  let (cto_files,input_files,template_file) = ErgoUtil.parse_args args_list usage args gconf in
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  List.iter (ErgoConfig.add_module_file gconf) input_files;
  begin match template_file with
  | None -> ()
  | Some t -> ErgoConfig.add_template_file gconf t
  end;
  let rctxt = make_init_rctxt gconf in
  welcome ();
  Js.export "ergotop"
    (object%js
      val initRCtxt = rctxt
      val version = Js.string ergo_version
      val buildate = Js.string Resources.builddate
      method runLine rctxt line =
        let (out, rctxt') = repl gconf rctxt (Js.to_string line) in
        Js.some
          (object%js
            val out = Js.string out
            val ctx = rctxt'
          end)
    end)

let wrap_error gconf e =
  let source_table = ErgoConfig.get_source_table gconf in
  begin match e with
  | Ergo_Error error ->
      new%js Js.error_constr (Js.string (string_of_error_with_table source_table error))
  | exn ->
      new%js Js.error_constr (Js.string (string_of_error_with_table source_table (ergo_system_error (Printexc.to_string exn))))
  end

let _ =
  let gconf = ErgoConfig.default_config () in
  begin try
    main gconf (ErgoUtil.patch_argv Sys.argv)
  with
  | e ->
      Js.raise_js_error (wrap_error gconf e)
  end


