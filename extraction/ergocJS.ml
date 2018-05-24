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

open ErgoUtil

let wrap_error e =
  begin match e with
  | Ergo_Error error ->
      new%js Js.error_constr (Js.string (string_of_error error))
  | exn ->
      new%js Js.error_constr (Js.string (string_of_error (ergo_system_error (Printexc.to_string exn))))
  end

let () =
  begin try
    Ergoc.main (fun x -> x) Sys.argv
  with
  | e ->
      Js.raise_js_error (wrap_error e)
  end


