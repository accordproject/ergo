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

Section ENames.
  Local Open Scope string.

  Section ScopedNames.
    Definition local_name : Set := string.
    Definition namespace_name : Set := string.
    Definition namespace_prefix : Set := option namespace_name.
    Definition absolute_name := string.

    Inductive name_ref : Set :=
    | RelativeRef : namespace_prefix -> local_name -> name_ref
    | AbsoluteRef : absolute_name -> name_ref.

    Definition absolute_name_of_local_name (ns: namespace_name) (ln: local_name) : absolute_name :=
      ns ++ "." ++ ln.

    Definition absolute_name_of_name_ref (local_ns: namespace_name) (nr: name_ref) : absolute_name :=
      match nr with
      | RelativeRef None ln => absolute_name_of_local_name local_ns ln
      | RelativeRef (Some ns) ln => absolute_name_of_local_name ns ln
      | AbsoluteRef an => an
      end.

    Definition absolute_ref_of_name_ref (local_ns: namespace_name) (nr: name_ref) : name_ref :=
      AbsoluteRef (absolute_name_of_name_ref local_ns nr).
    
  End ScopedNames.

  Section ReservedNames.
    Definition clause_main_name : local_name := "main". (* Main method -- defaults to dispatch over request *)
    Definition clause_init_name : local_name := "init". (* Init method -- defaults to setting default state *)

    (** This *)
    Definition this_contract := "contract". (* Contains all contract data and clause data *)
    Definition this_state := "state".       (* Contains state *)
    Definition this_emit := "emit".         (* Contains emit *)
    Definition this_response := "response". (* Contains response *)
    Definition local_state := "lstate".     (* Contains local state *)
    Definition local_emit := "lemit".       (* Contains local emit *)
    Definition current_time := "now".       (* Contains current time *)

  End ReservedNames.
  
  Section TypeNames.
    Definition request_type := "Request"%string.
    Definition response_type := "Response"%string.
    Definition event_type := "Event"%string.
  End TypeNames.
End ENames.
