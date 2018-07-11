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

open ErgoComp
open ParseUtil
open Unix

let get_stdlib () =
  List.map (ParseUtil.parse_ergo_module_from_string "stdlib") (List.map snd ErgoStdlib.ergo_stdlib)

let get_ctos () =
  ErgoConfig.get_ctos (ErgoConfig.default_config ())

let string_of_char_list cl = String.concat "" (List.map (String.make 1) cl)

let welcome () =
    if isatty stdin
    then print_string ("Welcome to ERGOTOP version " ^ (string_of_char_list ergo_version) ^ "\n")
    else ()

let prompt () =
    if isatty stdin then
        print_string "ergotop$ "
    else ()

let rec read_nonempty_line () =
    let line = read_line () in
    if line = "" then
        read_nonempty_line ()
    else
        line ^ "\n"

let rec repl (sctx, dctx) =
    prompt () ;
    try
        let decl = (ParseUtil.parse_ergo_declaration_from_string "stdin" (read_nonempty_line ())) in
        let result = ergo_eval_decl_via_calculus sctx dctx decl in
        let out = ergo_string_of_result result in
        if (List.length out) > 0
        then print_string ((string_of_char_list out) ^ "\n")
        else ();
        repl (ergo_maybe_update_context (sctx, dctx) result)
    with
    | ErgoUtil.Ergo_Error e ->
        print_string (ErgoUtil.string_of_error e);
        print_string "\n" ;
        repl (sctx, dctx)
    | End_of_file -> None

let main =
    welcome ();
    repl (ergo_make_stdlib_ctxt (get_ctos ()) (get_stdlib ()), ergo_empty_context)
