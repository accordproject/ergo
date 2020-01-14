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

let subst_amount get x1 s =
  let ms = get s in
  ignore(Re.Str.search_forward (Re.Str.regexp "0.0.\\(00?0?\\)") ms 0);
  let len = String.length (Re.Str.matched_group 1 ms) in
  let fmt =
    if len = 0
    then Printf.sprintf "%.0f"
    else if len = 1
    then Printf.sprintf "%.1f"
    else if len = 2
    then Printf.sprintf "%.2f"
    else Printf.sprintf"%.3f"
  in
  let vs = fmt x1 in
  let sep1 = String.sub ms 1 1 in
  let sep2 = String.sub ms 3 1 in
  let i = ref (String.sub vs 0 ((String.length vs)-(len+1))) in
  let d = String.sub vs ((String.length vs)-len) len in
  let res = ref (sep2 ^ d) in
  while String.length !i > 3 do
    res :=  sep1 ^ String.sub !i (String.length !i - 3) 3 ^ !res;
    i := String.sub !i 0 (String.length !i - 3)
  done;
  !i ^ !res

let amount_to_string_format x1 f =
  let re = Re.Str.regexp "\\(0.0.00?0?\\)" in
  Re.Str.global_substitute re (subst_amount (function s -> Re.Str.matched_group 1 s) x1) f

let subst_code get x1 s =
  x1

let subst_code_symbol get x1 s =
  begin match x1 with
  | "EUR" -> "€"
  | "GBP" -> "£"
  | "PLN" -> "zł"
  | "USD" -> "$"
  | "JPY" -> "¥"
  | _ -> x1 (* Defaults to ISO code *)
  end

let code_to_string_format x1 f =
  let code = Re.Str.string_after x1 ((String.length x1) - 3) in
  let re = Re.Str.regexp "\\(K\\)" in
  let f = Re.Str.global_substitute re (subst_code_symbol (function s -> Re.Str.matched_group 1 s) code) f in
  let re = Re.Str.regexp "\\(CCC\\)" in
  Re.Str.global_substitute re (subst_code (function s -> Re.Str.matched_group 1 s) code) f

