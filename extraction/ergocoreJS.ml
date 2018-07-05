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

(* builds the JS interface from ocaml *)

open Util
open ErgoUtil
open ErgoComp
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

let json_loc_of_loc loc =
  object%js
    val line = loc.line
    val character = loc.column
  end

let json_loc_missing () = json_loc_of_loc dummy_location.loc_start

let json_of_ergo_error error =
  object%js
    val kind = Js.string (error_kind error)
    val message= Js.string (error_message error)
    val locstart = json_loc_of_loc (error_loc_start error)
    val locend = json_loc_of_loc (error_loc_end error)
  end

let json_of_ergo_success () =
  object%js
    val kind = Js.string ""
    val message= Js.string ""
    val locstart = json_loc_missing ()
    val locend = json_loc_missing ()
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
      ergo_raise (ergo_system_error ("Couldn't load contract: "^(Printexc.to_string exn)))
    end
  in
  begin try
    let ergo_parsed = ergo_parse_module ("%JSBUFFER%",j_s) in
    let res = ErgoCompile.ergo_compile gconf (ref (get_stdlib ())) ergo_parsed in
    json_of_result res
  with
  | Ergo_Error error -> json_of_error error
  | exn -> json_of_error (ergo_system_error (Printexc.to_string exn))
  end

let ergo_version unit =
  ErgoUtil.ergo_version

let ergo_call contract =
  Js.string (ErgoUtil.ergo_call (Js.to_string contract##.name))

let _ =
  Js.export_all (object%js
    val call = Js.wrap_callback ergo_call
    val compile  = Js.wrap_callback ergo_compile
    val version = Js.wrap_callback ergo_version
  end)
