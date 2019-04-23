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

(* This module contains lexing utilities *)

(* Errors *)
exception LexError of string

(* Current file *)
val filename : string ref

(* Lexer Handler *)

type lex_state =
  | ExprState
  | TextState
  | VarState

type lex_handler

val lh_make_expr : unit -> lex_handler
val lh_make_text : unit -> lex_handler

val lh_in_template : lex_handler -> bool

val lh_reset_string : lex_handler -> unit

val lh_add_char_to_string : lex_handler -> char -> unit

val lh_get_string : lex_handler -> string

val lh_top_state : lex_handler -> lex_state

val lh_pop_state : lex_handler -> lex_state

val lh_push_state : lex_handler -> lex_state -> unit

