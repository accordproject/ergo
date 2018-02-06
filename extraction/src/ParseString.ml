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

open JComp.JuraCompiler

(*****************)
(* Generic Parse *)
(*****************)

let parse_string p_fun s =
  let buf = Lexing.from_string s in
  begin try
    p_fun buf
  with
  | Jura_Error msg -> raise (Jura_Error msg)
  | LexError msg ->
      Printf.fprintf stderr "[%s] in string%!\n" msg; raise (Jura_Error ("Parse error ["^ msg ^"] in string [" ^ s ^ "]"))
  | _ ->
      Printf.fprintf stderr "Error in string%!\n"; raise (Jura_Error ("Parse error [???] in string"))
  end

let parse_jura_from_string s : jura_package = parse_string parse_jura s
let parse_jurac_sexp_from_string s : jurac_package = parse_string parse_jurac_sexp s


