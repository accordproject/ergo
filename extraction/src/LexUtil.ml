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
open ErgoComp

(* Errors *)
exception LexError of string


(* String buffer *)
let string_buff () = Buffer.create 256
let reset_string buff = Buffer.clear buff
let add_char_to_string buff c = Buffer.add_char buff c
let get_string buff = Buffer.contents buff

(* Current file *)
let filename = ref ""

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
let current_template_input = {
  template_stack = Stack.create ();
  template_depth = ref 0;
}
let init_current_template_input () =
  Stack.clear current_template_input.template_stack;
  Stack.push ContractInput current_template_input.template_stack

let push_clause () =
  begin match Stack.top current_template_input.template_stack with
  | ContractInput -> Stack.push ClauseEnter current_template_input.template_stack
  | ClauseEnter
  | ClauseInput _ -> raise (LexError ("Cannot nest clause inside clause block"))
  | ListEnter
  | ListInput _ -> raise (LexError ("Cannot nest clause inside list block"))
  | OrderEnter
  | OrderInput _ -> raise (LexError ("Cannot nest clause inside order block"))
  | JoinEnter
  | JoinInput _ -> raise (LexError ("Cannot nest clause inside join block"))
  | WithEnter
  | WithInput _ -> raise (LexError ("Cannot nest clause inside with block"))
  | IfEnter
  | IfInput _ -> raise (LexError ("Cannot nest clause inside with block"))
  end

let push_list () =
  Stack.push ListEnter current_template_input.template_stack
let push_order () =
  Stack.push OrderEnter current_template_input.template_stack
let push_join () =
  Stack.push JoinEnter current_template_input.template_stack
let push_with () =
  Stack.push WithEnter current_template_input.template_stack
let push_if () =
  Stack.push IfEnter current_template_input.template_stack

let push_name name =
  begin match Stack.top current_template_input.template_stack with
  | ClauseEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      Stack.push (ClauseInput name) current_template_input.template_stack
  | ListEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      incr current_template_input.template_depth;
      Stack.push (ListInput name) current_template_input.template_stack
  | OrderEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      incr current_template_input.template_depth;
      Stack.push (OrderInput name) current_template_input.template_stack
  | JoinEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      Stack.push (JoinInput name) current_template_input.template_stack
  | WithEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      Stack.push (WithInput name) current_template_input.template_stack
  | IfEnter ->
      ignore(Stack.pop current_template_input.template_stack);
      Stack.push (IfInput name) current_template_input.template_stack
  | _ -> raise (LexError "Should be in open block")
  end

let pop_nested () =
  begin match Stack.pop current_template_input.template_stack with
  | ListInput _
  | OrderInput _ ->
      decr current_template_input.template_depth
  | _ -> ()
  end

let make_list_sep () =
  "\n" ^ String.make ((!(current_template_input.template_depth)) * 3) ' ' ^ "- "

let make_order_sep () =
  "\n" ^ String.make ((!(current_template_input.template_depth)) * 3) ' ' ^ "1. "

(* Lexer Handler *)

type lex_state =
  | ExprState
  | TextState
  | VarState
  | StartNestedState
  | EndNestedState

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

