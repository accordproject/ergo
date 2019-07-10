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

(* This module contains parsing utilities *)

open ErgoUtil
open LexUtil

open ErgoComp.ErgoCompiler

(** Generic parse *)
let parse parser lexer buf =
  begin try
    parser lexer buf
  with
  | LexError msg ->
      let start_pos = buf.Lexing.lex_start_p in
      let end_pos = buf.Lexing.lex_curr_p in
      ergo_raise (ergo_parse_error msg !filename start_pos end_pos)
  | _ ->
      let start_pos = buf.Lexing.lex_start_p in
      let end_pos = buf.Lexing.lex_curr_p in
      ergo_raise (ergo_parse_error "Parse error" !filename start_pos end_pos)
  end

let lexer_dispatch lh buf  =
  begin match lh_top_state lh with
  | ExprState -> ErgoLexer.token lh buf
  | TextState -> ErgoLexer.text lh buf
  | VarState -> ErgoLexer.var lh buf
  | StartNestedState -> ErgoLexer.startnested lh buf
  | EndNestedState -> ErgoLexer.endnested lh buf
  end

let parse_ergo_module f : ergo_module =
  init_current_template_input ();
  parse ErgoParser.main_module (lexer_dispatch (lh_make_expr ())) f
let parse_ergo_declarations f : ergo_declaration list =
  init_current_template_input ();
  parse ErgoParser.top_decls (lexer_dispatch (lh_make_expr ())) f
let parse_template f : ergo_expr =
  init_current_template_input ();
  parse ErgoParser.template (lexer_dispatch (lh_make_text ())) f

(** Parse from buffer *)
let parse_string p_fun s =
  let buf = Lexing.from_string s in
  p_fun buf

let parse_ergo_module_from_string fname s : ergo_module =
  filename := fname;
  parse_string parse_ergo_module s
let parse_ergo_declarations_from_string fname s : ergo_declaration list =
  filename := fname;
  parse_string parse_ergo_declarations s
let parse_template_from_string fname s : ergo_expr =
  filename := fname;
  parse_string parse_template s

let parse_cto_package_from_string fname s : cto_package =
  filename := unpatch_cto_extension fname;
  CtoImport.cto_import !filename (Cto_j.model_of_string s)

