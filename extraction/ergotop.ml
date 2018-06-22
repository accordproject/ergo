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

open ErgoComp
open ParseString

(*
let s = try (ParseString.parse_ergo_from_string "namespace org.accordproject.repl\ndefine variable a = 5\n" ; ())
    with ErgoUtil.Ergo_Error e -> print_string (ErgoUtil.string_of_error e); print_string "\n"
    *)

let string_of_char_list cl = String.concat "" (List.map (String.make 1) cl)

let p = print_string "ergotop$ "
let t = ParseString.parse_ergo_from_string ("namespace org.accordproject.repl\n" ^ (read_line ()) ^ "\n")
let u = ergo_eval_module ergo_empty_context t
let v = ergo_string_of_result u
let w = print_string (string_of_char_list v)
let n = print_string "\n"
