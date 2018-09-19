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
open ErgoComp.ErgoCompiler

type lang =
  | Ergo
  | ES5
  | ES6
  | Cicero
  | Java

let lang_of_name s =
  begin match s with
  | "ergo" -> Ergo
  | "es5" -> ES5
  | "es6" -> ES6
  | "cicero" -> Cicero
  | "java" -> Java
  | _ -> ergo_raise (ergo_system_error ("Unknown language: " ^ s))
  end

let name_of_lang s =
  begin match s with
  | Ergo -> "ergo"
  | ES5 -> "es5"
  | ES6 -> "es6"
  | Cicero -> "cicero"
  | Java -> "java"
  end

let extension_of_lang lang =
  begin match lang with
  | Ergo -> ".ergo"
  | ES5 -> "_es5.js"
  | ES6 -> ".js"
  | Cicero -> "_cicero.js"
  | Java -> ".java"
  end

let can_link_runtime lang =
  begin match lang with
  | Ergo -> false
  | ES5 -> true
  | ES6 -> true
  | Cicero -> true
  | Java -> false
  end

let targets = [ES5;ES6;Cicero;Java]

let available_targets =
  "(available: " ^ (String.concat "," (List.map name_of_lang targets)) ^ ")"

type global_config = {
  mutable econf_source : lang;
  mutable econf_target : lang;
  mutable econf_sources_text : (string * string) list;
  mutable econf_ctos : cto_package list;
  mutable econf_modules : ergo_module list;
  mutable econf_link : bool;
}

let empty_config () = {
  econf_source = Ergo;
  econf_target = ES6;
  econf_sources_text = [];
  econf_ctos = [];
  econf_modules = [];
  econf_link = false;
} 

let get_source_lang gconf = gconf.econf_source
let get_target_lang gconf = gconf.econf_target
let get_ctos gconf = gconf.econf_ctos
let get_modules gconf = gconf.econf_modules
let get_all gconf =
  (List.map (fun x -> ErgoComp.InputCTO x) (get_ctos gconf))
  @ (List.map (fun x -> ErgoComp.InputErgo x) (get_modules gconf))
let get_all_sorted gconf =
  topo_sort_inputs (get_all gconf)

let set_source_lang gconf s = gconf.econf_source <- (lang_of_name s)
let set_target_lang gconf s = gconf.econf_target <- (lang_of_name s)
let add_source_text gconf f fcontent =
  gconf.econf_sources_text <-  (f,fcontent) :: gconf.econf_sources_text
let add_cto gconf cto =
  gconf.econf_ctos <-  gconf.econf_ctos @ [cto]
let add_cto_file gconf (f,fcontent) =
  add_source_text gconf f fcontent;
  add_cto gconf (ParseUtil.parse_cto_package_from_string f fcontent)
let add_module gconf m =
  gconf.econf_modules <- gconf.econf_modules @ [m]
let add_module_file gconf (f,fcontent) =
  add_source_text gconf f fcontent;
  add_module gconf (ParseUtil.parse_ergo_module_from_string f fcontent)

let get_stdlib () =
  let stdctos = ErgoStdlib.ergo_stdcto in
  let stdlib = ErgoStdlib.ergo_stdlib in
  (stdctos@stdlib,
   Util.map_assoc ParseUtil.parse_cto_package_from_string stdctos,
   Util.map_assoc ParseUtil.parse_ergo_module_from_string stdlib)

let add_stdlib gconf =
  let (sources,ctos,mls) = get_stdlib () in
  gconf.econf_sources_text <- sources @  gconf.econf_sources_text;
  gconf.econf_ctos <- ctos @ gconf.econf_ctos;
  gconf.econf_modules <- mls @ gconf.econf_modules
let default_config () =
  let gconf = empty_config () in
  add_stdlib gconf;
  gconf

let get_source_table gconf = gconf.econf_sources_text

let set_link gconf () = gconf.econf_link <- true
let should_link gconf =
  if gconf.econf_link
  then
    if can_link_runtime gconf.econf_target
    then true
    else ergo_raise
           (ergo_system_error
              ("Cannot link for target: " ^ (name_of_lang gconf.econf_target)))
  else
    false
