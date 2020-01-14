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

open Ergo_lib
open ErgoUtil

let wrap_error gconf e =
  let source_table = ErgoConfig.get_source_table gconf in
  begin match e with
  | ErgoUtil.Ergo_Error error ->
      Printf.eprintf "%s\n"
        (ErgoUtil.string_of_error_with_table source_table error);
      exit 2
  | exn ->
      Printf.eprintf "%s\n"
        (ErgoUtil.string_of_error_with_table source_table
           (ErgoUtil.ergo_system_error (Printexc.to_string exn)));
      exit 2
  end

let _ =
  let gconf = ErgoConfig.default_config () in
  begin try
    Main.main gconf (patch_argv Sys.argv)
  with
  | e ->
      wrap_error gconf e
  end

