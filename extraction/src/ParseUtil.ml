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
  try
    parser lexer buf
  with
  | LexError msg ->
      begin
        let pos = buf.Lexing.lex_start_p in
        let msg = Printf.sprintf "At line %d column %d: %s%!" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) msg in
        ergo_raise (ergo_parse_error msg)
      end
  | _ ->
      begin
        let pos = buf.Lexing.lex_start_p in
        let msg = Printf.sprintf "At line %d column %d: syntax error%!" pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) in
        ergo_raise (ergo_parse_error msg)
      end

let parse_ergo f : ergo_package = parse ErgoParser.main (ErgoLexer.token (string_buff ())) f

