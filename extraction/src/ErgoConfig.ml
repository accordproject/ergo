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

type lang =
  | Ergo
  | JavaScript
  | Calculus

let lang_of_name s =
  begin match s with
  | "ergo" -> Ergo
  | "javascript" -> JavaScript
  | "calculus" -> Calculus
  | _ -> raise (Ergo_Error ("Unknown language: " ^ s))
  end

let name_of_lang s =
  begin match s with
  | Ergo -> "ergo"
  | JavaScript -> "javascript"
  | Calculus -> "calculus"
  end

let extension_of_lang lang =
  begin match lang with
  | Ergo -> ".ergo"
  | JavaScript -> ".js"
  | Calculus -> ".ergoc"
  end
    
type global_config = {
    mutable jconf_source : lang;
    mutable jconf_target : lang;
    mutable jconf_contract_name : string option;
    mutable jconf_clause_name : string option;
    mutable jconf_with_dispatch : bool;
    mutable jconf_cto_file : string option;
    mutable jconf_cto : ErgoComp.cto_package option;
  }

let default_config () = {
  jconf_source = Ergo;
  jconf_target = JavaScript;
  jconf_contract_name = None;
  jconf_clause_name = None;
  jconf_with_dispatch = false;
  jconf_cto_file = None;
  jconf_cto = None;
} 

let get_source_lang gconf = gconf.jconf_source
let get_target_lang gconf = gconf.jconf_target
let get_contract_name gconf = gconf.jconf_contract_name
let get_clause_name gconf = gconf.jconf_clause_name
let get_with_dispatch gconf = gconf.jconf_with_dispatch
let get_cto_file gconf = gconf.jconf_cto_file
let get_cto gconf = gconf.jconf_cto

let set_source_lang gconf s = gconf.jconf_source <- (lang_of_name s)
let set_target_lang gconf s = gconf.jconf_target <- (lang_of_name s)
let set_contract_name gconf s = gconf.jconf_contract_name <- Some s
let set_clause_name gconf s = gconf.jconf_clause_name <- Some s
let set_with_dispatch gconf b = gconf.jconf_with_dispatch <- b
let set_with_dispatch_true gconf () = gconf.jconf_with_dispatch <- true
let set_with_dispatch_false gconf () = gconf.jconf_with_dispatch <- false
let set_cto gconf s =
  gconf.jconf_cto <- Some (CtoImport.cto_import (Cto_j.model_of_string s))
let set_cto_file gconf s =
  begin
    gconf.jconf_cto_file <- Some s;
    set_cto gconf (Util.string_of_file s)
  end
