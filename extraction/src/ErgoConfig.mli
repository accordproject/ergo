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

open ErgoComp.ErgoCompiler

type lang =
  | Ergo
  | ES5
  | ES6
  | Cicero
  | Java

val lang_of_target : string -> lang
val name_of_lang : lang -> string
val extension_of_lang : lang -> string
val script_lang_of_target : string -> string

val available_targets : string list
val available_targets_message : string

type global_config = {
  mutable econf_source : lang;
  mutable econf_target : lang;
  mutable econf_source_template : (string * string) option;
  mutable econf_sources_text : (string * string) list;
  mutable econf_template : (string * ergo_expr) option;
  mutable econf_ctos : cto_package list;
  mutable econf_modules : ergo_module list;
  mutable econf_link : bool;
  mutable econf_warnings : bool;
}

val default_config : unit -> global_config

val get_source_lang : global_config -> lang
val get_target_lang : global_config -> lang
val get_template : global_config -> (string * ergo_expr) option
val get_ctos : global_config -> cto_package list
val get_modules : global_config -> ergo_module list
val get_all : global_config -> ergo_input list
val get_all_sorted : global_config -> ergo_input list

val set_source_lang : global_config -> string -> unit
val set_target_lang : global_config -> string -> unit

val add_template_file : global_config -> string * string -> unit
val add_cto_file : global_config -> string * string -> unit
val add_module_file : global_config -> string * string -> unit

val get_source_table : global_config -> (string * string) list

val set_link : global_config -> unit -> unit

val should_link : global_config -> bool

val set_warnings : global_config -> unit -> unit

