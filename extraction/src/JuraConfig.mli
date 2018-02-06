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

type lang =
  | Jura
  | JavaScript
  | Calculus

val lang_of_name : string -> lang
val name_of_lang : lang -> string
val extension_of_lang : lang -> string

type global_config = {
    mutable jconf_source : lang;
    mutable jconf_target : lang;
    mutable jconf_contract_name : string option;
    mutable jconf_clause_name : string option
  }

val default_config : unit -> global_config

val get_source_lang : global_config -> lang
val get_target_lang : global_config -> lang
val get_contract_name : global_config -> string option    
val get_clause_name : global_config -> string option    

val set_source_lang : global_config -> string -> unit
val set_target_lang : global_config -> string -> unit
val set_contract_name : global_config -> string -> unit
val set_clause_name : global_config -> string -> unit

