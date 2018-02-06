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

(**********)
(* Errors *)
(**********)
    
exception LexError of string


(*****************)
(* String buffer *)
(*****************)

let string_buff () = Buffer.create 256
let reset_string buff = Buffer.clear buff
let add_char_to_string buff c = Buffer.add_char buff c
let get_string buff = Buffer.contents buff

