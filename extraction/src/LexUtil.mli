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

(* Current input for templates *)
type template_input =
  | ContractInput
  | ClauseEnter
  | ClauseInput of string
  | ListEnter
  | ListInput of string
  | OrderEnter
  | OrderInput of string
  | JoinEnter
  | JoinInput of string
  | WithEnter
  | WithInput of string
  | IfEnter
  | IfInput of string

type template_state = {
    template_stack: template_input Stack.t;
    template_depth: int ref;
  }

val current_template_input : template_state
val init_current_template_input : unit -> unit

val push_clause : unit -> unit
val push_list : unit -> unit
val push_order : unit -> unit
val push_join : unit -> unit
val push_with : unit -> unit
val push_if : unit -> unit
val push_name : string -> unit
val pop_nested : unit -> unit

val make_list_sep : unit -> string
val make_order_sep : unit -> string

(* Lexer Handler *)

type lex_state =
  | ExprState
  | TextState
  | VarState
  | StartNestedState
  | EndNestedState

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

