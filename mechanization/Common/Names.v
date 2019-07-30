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

Require Import String.

Section Names.
  Local Open Scope string.

  Section ScopedNames.
    Definition local_name : Set := string.
    Definition namespace_name : Set := string.
    Definition namespace_prefix : Set := option namespace_name.

    Definition relative_name : Set := namespace_prefix * local_name.
    Definition absolute_name : Set := string.

    Definition absolute_name_of_local_name (ns: namespace_name) (ln: local_name) : absolute_name :=
      ns ++ "." ++ ln.

    Definition absolute_name_of_relative_name (local_ns: namespace_name) (rn: relative_name) : absolute_name :=
      match rn with
      | (None,ln) => absolute_name_of_local_name local_ns ln
      | (Some ns,ln) => absolute_name_of_local_name ns ln
      end.

  End ScopedNames.

  Section ReservedNames.
    Definition clause_main_name : local_name := "main". (* Main method -- defaults to dispatch over request *)
    Definition clause_init_name : local_name := "init". (* Init method -- defaults to setting default state *)

    (** This *)
    Definition this_this := "this".         (* Context-dependent current value -- for templates *)
    Definition this_contract := "contract". (* Contains all contract data and clause data *)
    Definition this_state := "state".       (* Contains state *)
    Definition this_emit := "emit".         (* Contains emit *)
    Definition this_response := "response". (* Contains response *)
    Definition local_state := "lstate".     (* Contains local state *)
    Definition local_emit := "lemit".       (* Contains local emit *)
    Definition current_time := "now".       (* Contains current time *)

  End ReservedNames.
  
  Section TypeNames.
    Definition accordproject_base_namespace : string := "org.accordproject.base"%string.
    Definition accordproject_runtime_namespace : string := "org.accordproject.cicero.runtime"%string.
    Definition accordproject_contract_namespace : string := "org.accordproject.cicero.contract"%string.
    Definition accordproject_stdlib_namespace : string := "org.accordproject.ergo.stdlib"%string.
    Definition accordproject_time_namespace : string := "org.accordproject.time"%string.
    Definition accordproject_markdown_namespace : string := "org.accordproject.markdown"%string.
    Definition accordproject_ergotop_namespace : string := "org.accordproject.ergo.top"%string.

    (* Accord Project system types *)
    Definition default_event_absolute_name : string :=
      absolute_name_of_local_name accordproject_base_namespace "Event".
    Definition default_transaction_absolute_name : string :=
      absolute_name_of_local_name accordproject_base_namespace "Transaction".
    Definition default_asset_absolute_name : string :=
      absolute_name_of_local_name accordproject_base_namespace "Asset".
    Definition default_participant_absolute_name : string :=
      absolute_name_of_local_name accordproject_base_namespace "Participant".

    (* Accord Project common types *)
    Definition default_request_absolute_name : string :=
      absolute_name_of_local_name accordproject_runtime_namespace "Request".
    Definition default_response_absolute_name : string :=
      absolute_name_of_local_name accordproject_runtime_namespace "Response".
    Definition default_state_absolute_name : string :=
      absolute_name_of_local_name accordproject_contract_namespace "AccordContractState".

    (* Ergo types *)
    Definition default_error_absolute_name : string :=
      absolute_name_of_local_name accordproject_stdlib_namespace "ErgoErrorResponse".

  End TypeNames.

  Section Misc.
    Definition function_name_in_table (tname:option string) (fname:string) : string :=
      match tname with
      | None => fname
      | Some tname => tname ++ "_" ++ fname
      end.
  End Misc.

  Section Namespaces.
    Definition no_namespace : string := "".
  End  Namespaces.

End Names.
