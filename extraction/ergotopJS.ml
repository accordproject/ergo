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

(* REPL *)

let repl rctxt text =
  try
      let decls = ParseUtil.parse_ergo_declarations_from_string "stdin" text in
      List.fold_left
        (fun (answer,rctxt) decl ->
           begin
             (* eval *)
             let (out,rctxt') = ErgoTopUtil.my_ergo_repl_eval_decl rctxt decl in
             (* print *)
             (answer ^ (ErgoUtil.wrap_jerrors Util.string_of_char_list out), rctxt')
           end)
        ("",rctxt) decls
  with
    ErgoUtil.Ergo_Error e -> (ErgoUtil.string_of_error_with_source text e ^ "\n", rctxt)

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

(* Initialize the REPL ctxt, catching errors in input CTOs and modules *)
let safe_init_repl_ctxt inputs =
  ErgoUtil.wrap_jerrors
    (fun x -> x)
    (ErgoTopUtil.my_init_repl_context inputs)

let make_init_rctxt =
  let gconf = ErgoConfig.default_config () in
  (*
  let (cto_files,input_files) = ErgoUtil.parse_args args_list usage args gconf in
  List.iter (ErgoConfig.add_cto_file gconf) cto_files;
  List.iter (ErgoUtil.process_file (ErgoConfig.add_module_file gconf)) input_files;
  *)
  (*
  let ctos = ErgoConfig.get_ctos gconf in
  let modules = ErgoConfig.get_modules gconf in
  *)
  let all_modules = ErgoConfig.get_all_sorted gconf in
  let rctxt = safe_init_repl_ctxt all_modules in
  rctxt

let _ =
  Js.export "ergotop"
    (object%js
       val initRCtxt = make_init_rctxt
       method runLine rctxt line =
         let (out, rctxt') = repl rctxt (Js.to_string line) in
         Js.some
           (object%js
             val out = Js.string out
             val ctx = rctxt'
           end)
     end)
