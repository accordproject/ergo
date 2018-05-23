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

open Util
open ErgoUtil
open ErgoCompile
open ErgoConfig

(**********************************)
(* Configuration support          *)
(**********************************)

(* XXX g is applied to json value if it exists, f is the configuration setter, taking the result of g XXX *)
let apply_gen gconf f g o = Js.Optdef.iter o (fun j -> f gconf (g j))
let apply gconf f o = apply_gen gconf f Js.to_string o
let iter_array_gen gconf f o = Js.Optdef.iter o (fun a -> f gconf a)
let iter_array gconf f o =
  iter_array_gen gconf
    (fun gconf a ->
       let a = Js.str_array a in
       ignore (Js.array_map (fun s -> f gconf (Js.to_string s)) a)) o

(**********************************)
(* Equivalent to qcert cmd        *)
(**********************************)

let global_config_of_json j =
  let gconf = default_config () in
  (* Specialize apply/iter for this given gconf *)
  let apply = apply gconf in
  let iter_array = iter_array gconf in
  (* CTOs *)
  iter_array ErgoConfig.add_cto j##.cto;
  (* Target *)
  apply ErgoConfig.set_target_lang j##.target;
  gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_of_ergo_error error =
  object%js
    val kind = Js.string (error_kind error)
    val message= Js.string (error_message error)
  end

let json_of_ergo_success () =
  object%js
    val kind = Js.string ""
    val message= Js.string ""
  end

let json_of_result res =
  object%js
    val error = json_of_ergo_success ()
    val result = Js.string res
    val code = Js.bool false
  end

let json_of_error error =
  object%js
    val error = json_of_ergo_error error
    val result = Js.string ""
    val code = Js.bool true
  end

let ergo_compile input =
  begin try
    let gconf =
      begin try
        global_config_of_json input
      with exn ->
        ergo_raise (ergo_system_error ("Couldn't load configuration: "^(Printexc.to_string exn)))
      end
    in
    let j_s =
      begin try
        Js.to_string input##.ergo
      with exn ->
        ergo_raise (ergo_system_error ("[Compilation Error] Couldn't load contract: "^(Printexc.to_string exn)))
      end
    in
    let res = ErgoCompile.ergo_compile gconf j_s in
    json_of_result res
  with
  | Ergo_Error error -> json_of_error error
  | exn -> json_of_error (ergo_system_error (Printexc.to_string exn))
  end

let ergo_version unit =
  ErgoUtil.ergo_version

let _ =
  Js.export "Ergo" (object%js
    val compile  = Js.wrap_callback ergo_compile
    val version = Js.wrap_callback ergo_version
  end)
