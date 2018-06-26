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
  | JavaScript
  | JavaScriptCicero
  | Java

let lang_of_name s =
  begin match s with
  | "ergo" -> Ergo
  | "javascript" -> JavaScript
  | "javascript_cicero" -> JavaScriptCicero
  | "java" -> Java
  | _ -> ergo_raise (ergo_system_error ("Unknown language: " ^ s))
  end

let name_of_lang s =
  begin match s with
  | Ergo -> "ergo"
  | JavaScript -> "javascript"
  | JavaScriptCicero -> "javascript_cicero"
  | Java -> "java"
  end

let extension_of_lang lang =
  begin match lang with
  | Ergo -> ".ergo"
  | JavaScript -> ".js"
  | JavaScriptCicero -> ".js"
  | Java -> ".java"
  end

let targets = [JavaScript;JavaScriptCicero (* ;Java *)]

let available_targets =
  "(available: " ^ (String.concat "," (List.map name_of_lang targets)) ^ ")"

type global_config = {
  mutable jconf_source : lang;
  mutable jconf_target : lang;
  mutable jconf_cto_files : string list;
  mutable jconf_ctos : cto_package list;
}

let default_config () = {
  jconf_source = Ergo;
  jconf_target = JavaScript;
  jconf_cto_files = [];
  jconf_ctos = [];
} 

let get_source_lang gconf = gconf.jconf_source
let get_target_lang gconf = gconf.jconf_target
let get_cto_files gconf = gconf.jconf_cto_files
let get_ctos gconf = gconf.jconf_ctos

let set_source_lang gconf s = gconf.jconf_source <- (lang_of_name s)
let set_target_lang gconf s = gconf.jconf_target <- (lang_of_name s)
let add_cto gconf s =
  gconf.jconf_ctos <- gconf.jconf_ctos @ [CtoImport.cto_import (Cto_j.model_of_string s)]
let add_cto_file gconf (f,s) =
  begin
    gconf.jconf_cto_files <- gconf.jconf_cto_files @ [s];
    add_cto gconf s
  end
