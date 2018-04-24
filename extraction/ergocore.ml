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
  (* CTO *)
  iter_array ErgoConfig.add_cto j##.cto;
  (* Source/Target *)
  apply ErgoConfig.set_source_lang j##.source;
  apply ErgoConfig.set_target_lang j##.target;
  (* Dispatch option *)
  Js.Optdef.iter j##.withdispatch (fun b -> ErgoConfig.set_with_dispatch gconf (Js.to_bool b));
  (* Contract/Clause Names *)
  Js.Optdef.iter j##.contract (fun s -> ErgoConfig.set_contract_name gconf (Js.to_string s));
  Js.Optdef.iter j##.clause (fun s -> ErgoConfig.set_clause_name gconf (Js.to_string s));
  gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_of_result res =
  object%js
    val result = Js.string res
    val error = Js.bool false
  end

let json_of_error msg =
  object%js
    val result = Js.string msg
    val error = Js.bool true
  end

let ergo_compile input =
  begin try
    let gconf =
      begin try
        global_config_of_json input
      with exn ->
        raise (Ergo_Error ("[Compilation Error] Couldn't load configuration: "^(Printexc.to_string exn)))
      end
    in
    let j_s =
      begin try
        Js.to_string input##.ergo
      with exn ->
        raise (Ergo_Error ("[Compilation Error] Couldn't load contract: "^(Printexc.to_string exn)))
      end
    in
    let res =
      begin try ErgoCompile.ergo_compile gconf j_s
        with Ergo_Error err -> raise (Ergo_Error err)
        | exn -> raise (Ergo_Error ("[Compilation Error] "^(Printexc.to_string exn)))
      end
    in
    json_of_result res
  with
  | Ergo_Error msg -> json_of_error msg
  | exn -> json_of_error ("[Main error: "^(Printexc.to_string exn)^"]")
  end

let ergo_version unit =
  ErgoUtil.ergo_version

let _ =
  Js.export "Ergo" (object%js
    val compile  = Js.wrap_callback ergo_compile
    val version = Js.wrap_callback ergo_version
  end)
