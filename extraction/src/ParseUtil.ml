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


(*****************)
(* Generic Parse *)
(*****************)

let parse parser lexer buf =
  begin try
    parser lexer buf
  with
  | LexError msg ->
      let start_pos = buf.Lexing.lex_start_p in
      let end_pos = buf.Lexing.lex_curr_p in
      ergo_raise (ergo_parse_error msg start_pos end_pos)
  | _ ->
      let start_pos = buf.Lexing.lex_start_p in
      let end_pos = buf.Lexing.lex_curr_p in
      ergo_raise (ergo_parse_error "Parse error" start_pos end_pos)
  end

let parse_ergo_module f : ergo_module = parse ErgoParser.main_module (ErgoLexer.token (string_buff ())) f
let parse_ergo_declaration f : ergo_declaration = parse ErgoParser.main_decl (ErgoLexer.token (string_buff ())) f

