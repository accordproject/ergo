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

(**********)
(* Errors *)
(**********)

exception LexError of string


(*****************)
(* String buffer *)
(*****************)

val string_buff : unit -> Buffer.t
val reset_string : Buffer.t -> unit
val add_char_to_string : Buffer.t -> char -> unit
val get_string : Buffer.t -> string


