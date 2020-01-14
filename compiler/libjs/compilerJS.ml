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

open Js_of_ocaml

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
let apply_bool gconf f o = apply_gen gconf f Js.to_bool o
let iter_array_gen gconf f o =
  Js.Optdef.iter o (fun a -> f gconf a)
let iter_array gconf f o =
  iter_array_gen gconf
    (fun gconf a ->
       let a = Js.str_array a in
       ignore (Js.array_map (fun s -> f gconf (Js.to_string s)) a)) o
let iter_inputs gconf f g h o =
  iter_array_gen gconf
    (fun gconf a ->
       ignore (Js.array_map (fun x -> f gconf (Js.to_string (g x), Js.to_string (h x))) a)) o
let iter_template gconf f g h o =
  iter_array_gen gconf
    (fun gconf a ->
       ignore (Js.Opt.iter a (fun x -> f gconf (Js.to_string (g x), Js.to_string (h x))))) o

(**********************************)
(* Equivalent to qcert cmd        *)
(**********************************)

let global_config_of_json gconf j =
  (* Specialize apply/iter for this given gconf *)
  let apply = apply gconf in
  let apply_bool = apply_bool gconf in
  let iter_inputs = iter_inputs gconf in
  let iter_template = iter_template gconf in
  (* Template *)
  iter_template (fun gconf x -> ErgoConfig.add_template_file gconf x)
    (fun x -> x##.name)
    (fun x -> x##.content)
    j##.sourceTemplate;
  (* CTOs *)
  iter_inputs (fun gconf x -> ErgoConfig.add_cto_file gconf x)
    (fun x -> x##.name)
    (fun x -> x##.content)
    j##.cto;
  (* Ergos *)
  iter_inputs (fun gconf x -> ErgoConfig.add_module_file gconf x)
    (fun x -> x##.name)
    (fun x -> x##.content)
    j##.ergo;
  (* Target *)
  apply_bool (fun gconf b -> if b then ErgoConfig.set_link gconf ()) j##.link;
  apply ErgoConfig.set_target_lang j##.target;
  gconf

let wrap_all wrap_f l =
  let a = new%js Js.array_empty in
  List.iter (fun x -> ignore (a##push (wrap_f x))) l;
  a

let json_loc_of_loc loc =
  object%js
    val line = loc.line
    val column = loc.column
  end

let json_loc_missing () = json_loc_of_loc dummy_location.loc_start

let json_loc_file f =
  begin match f with
  | None -> Js.null
  | Some file -> Js.some (Js.string file)
  end

let json_of_ergo_error gconf error =
  let source_table = ErgoConfig.get_source_table gconf in
  object%js
    val kind = Js.string (error_kind error)
    val message= Js.string (error_message error)
    val fileName = json_loc_file (error_loc_file error)
    val locstart = json_loc_of_loc (error_loc_start error)
    val locend = json_loc_of_loc (error_loc_end error)
    val fullMessage = Js.string (string_of_error_with_table source_table error)
  end

let json_of_ergo_success () =
  object%js
    val kind = Js.string ""
    val message= Js.string ""
    val fileName = Js.null
    val locstart = json_loc_missing ()
    val locend = json_loc_missing ()
    val fullMessage = Js.string ""
  end

let json_of_result res warnings =
  let warningsArr = Array.of_list (List.map Js.string warnings) in
  object%js
    val error = json_of_ergo_success ()
    val result = Js.string res
    val code = Js.bool false
    val contractName = Js.null
    val warnings = Js.array warningsArr
  end

let json_of_result_with_contract_name cn res warnings =
  let warningsArr = Array.of_list (List.map Js.string warnings) in
  object%js
    val error = json_of_ergo_success ()
    val result = Js.string res
    val code = Js.bool false
    val contractName = Js.some (Js.string cn)
    val warnings = Js.array warningsArr
  end

let json_of_error gconf error =
  object%js
    val error = json_of_ergo_error gconf error
    val result = Js.string ""
    val code = Js.bool true
    val contractName = Js.null
    val warnings = Js.array [||]
  end

let ergo_compile input =
  let gconf = default_config () in
  begin try
    let gconf = global_config_of_json gconf input in
    let target_lang = ErgoConfig.get_target_lang gconf in
    let template = ErgoConfig.get_template gconf in
    let all_modules = ErgoConfig.get_all_sorted gconf in
    let (contract_name,file,res,warnings) = ErgoCompile.ergo_compile target_lang all_modules template in
    let source_table = ErgoConfig.get_source_table gconf in
    let warnings = string_of_warnings_with_table source_table warnings in
    let res = ErgoCompile.ergo_link gconf res in
    begin match contract_name with
    | None -> json_of_result res warnings
    | Some cn -> json_of_result_with_contract_name cn res warnings
    end
  with
  | Ergo_Error error -> json_of_error gconf error
  | exn -> json_of_error gconf (ergo_system_error (Printexc.to_string exn))
  end

let ergo_version unit =
  ErgoUtil.ergo_version

let ergo_call contract =
  Js.string (ErgoUtil.ergo_call (Js.to_string contract##.name))

let lang_of_target s =
  Js.string (ErgoConfig.script_lang_of_target (Js.to_string s))

let available_targets () =
  let a = Array.of_list ErgoConfig.available_targets in
  let a_js = Array.map (fun x -> Js.string x) a in
  Js.array a_js

let _ =
  Js.export_all (object%js
    val call = Js.wrap_callback ergo_call
    val compile  = Js.wrap_callback ergo_compile
    val langoftarget = Js.wrap_callback lang_of_target
    val availabletargets = Js.wrap_callback available_targets
    val version = Js.wrap_callback ergo_version
  end)
