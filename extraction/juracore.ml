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
open JuraCompile
open JuraConfig

(**********************************)
(* Configuration support          *)
(**********************************)

(* XXX g is applied to json value if it exists, f is the configuration setter, taking the result of g XXX *)
let apply_gen gconf f g o = Js.Optdef.iter o (fun j -> f gconf (g j))
let apply gconf f o = apply_gen gconf f Js.to_string o

(**********************************)
(* Equivalent to qcert cmd        *)
(**********************************)

let global_config_of_json j =
  let gconf = default_config () in
  (* Specialize apply/iter for this given gconf *)
  let apply = apply gconf in
  (* CTO *)
  apply JuraConfig.set_cto j##.cto;
  (* Source/Target *)
  apply JuraConfig.set_source_lang j##.source;
  apply JuraConfig.set_target_lang j##.target;
  (* Dispatch option *)
  Js.Optdef.iter j##.withdispatch (fun b -> JuraConfig.set_with_dispatch gconf (Js.to_bool b));
  (* Contract/Clause Names *)
  Js.Optdef.iter j##.contract (fun s -> JuraConfig.set_contract_name gconf (Js.to_string s));
  Js.Optdef.iter j##.clause (fun s -> JuraConfig.set_clause_name gconf (Js.to_string s));
  gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_of_result res =
  object%js
    val result = Js.string res
  end

let json_of_error msg =
  object%js
    val result = Js.string msg
  end

let jura_compile input =
  begin try
    let gconf =
      begin try
	global_config_of_json input
      with exn ->
        raise (Jura_Error ("[Couldn't load configuration: "^(Printexc.to_string exn)^"]"))
      end
    in
    let j_s =
      begin try
       Js.to_string input##.jura
      with exn ->
        raise (Jura_Error ("[Couldn't load contract: "^(Printexc.to_string exn)^"]"))
      end
    in
    let res =
      begin try
        JuraCompile.jura_compile gconf j_s
      with Jura_Error err -> raise (Jura_Error ("[Compilation error: "^err^"]"))
      | exn -> raise (Jura_Error ("[Compilation error: "^(Printexc.to_string exn)^"]"))
      end
    in
    json_of_result res
  with
  | Jura_Error msg -> json_of_error msg
  | exn -> json_of_error ("[Main error: "^(Printexc.to_string exn)^"]")
  end

let _ =
  Js.export "Jura" (object%js
    val compile  = Js.wrap_callback jura_compile
   end)
