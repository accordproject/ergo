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
  begin try
    p_fun buf
  with
  | Ergo_Error msg -> raise (Ergo_Error msg)
  | LexError msg ->
      Printf.fprintf stderr "[%s] in string%!\n" msg; raise (Ergo_Error ("Parse error ["^ msg ^"] in string [" ^ s ^ "]"))
  | _ ->
      Printf.fprintf stderr "Error in string%!\n"; raise (Ergo_Error ("Parse error [???] in string"))
  end

let parse_ergo_from_string s : ergo_package = parse_string parse_ergo s
let parse_ergoc_sexp_from_string s : ergoc_package = parse_string parse_ergoc_sexp s


