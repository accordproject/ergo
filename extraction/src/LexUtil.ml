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

open Util

(* Errors *)
exception LexError of string


(* String buffer *)
let string_buff () = Buffer.create 256
let reset_string buff = Buffer.clear buff
let add_char_to_string buff c = Buffer.add_char buff c
let get_string buff = Buffer.contents buff

(* Current file *)
let filename = ref ""

(* Lexer Handler *)

type lex_state =
  | ExprState
  | TextState
  | VarState

type lex_handler =
    { buffer: Buffer.t;
      state: lex_state Stack.t;
      in_template: bool }

let lh_make s_init tem =
  let st = Stack.create () in
  begin
    Stack.push s_init st;
    { buffer = string_buff();
      state = st;
      in_template = tem }
  end

let lh_make_expr () =
  lh_make ExprState false
let lh_make_text () =
  lh_make TextState true

let lh_in_template lh =
  lh.in_template

let lh_reset_string lh =
  reset_string lh.buffer

let lh_add_char_to_string lh c =
  add_char_to_string lh.buffer c

let lh_get_string lh =
  get_string lh.buffer

let lh_top_state lh =
  Stack.top lh.state
let lh_pop_state lh =
  Stack.pop lh.state
let lh_push_state lh s =
  Stack.push s lh.state
