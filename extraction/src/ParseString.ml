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

open Util
open LexUtil
open ParseUtil

open ErgoComp.ErgoCompiler

(*****************)
(* Generic Parse *)
(*****************)

let parse_string p_fun s =
  let buf = Lexing.from_string s in
  p_fun buf

let parse_ergo_module_from_string fname s : ergo_module = parse_string parse_ergo_module s
let parse_ergo_declaration_from_string fname s : ergo_declaration = parse_string parse_ergo_declaration s

