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

(* Error monad *)

Require Import String.
Require Import List.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ZArith.

Section EResult.
  Record location_point :=
    mkLocationPoint {
        offset: Z;
        line : Z;
        column : Z;
      }.
  Record location :=
    mkLocation {
        loc_start: location_point;
        loc_end: location_point;
      }.
  Definition dummy_location : location :=
    let dummy_location_point := mkLocationPoint (-1) (-1) (-1) in
    mkLocation dummy_location_point dummy_location_point.

  Record parse_error :=
    mkParseError {
        parse_error_message: string;
        parse_error_location: location;
      }.
  
  Inductive eerror : Set :=
  | SystemError : string -> eerror
  | ParseError : parse_error -> eerror
  | CompilationError : string -> eerror
  | TypeError : string -> eerror
  | RuntimeError : string -> eerror.

  Definition eresult (A:Set) := Result A eerror.
  Definition esuccess {A:Set} (a:A) : eresult A :=
    Success A eerror a.
  Definition efailure {A:Set} (e:eerror) : eresult A :=
    Failure A eerror e.
  Definition eolift {A B:Set} (f:A -> eresult B) (a:eresult A) : eresult B :=
    lift_failure f a.
  Definition elift {A B:Set} (f:A -> B) (a:eresult A) : eresult B :=
    lift_failure_in f a.
  Definition elift2 {A B C:Set} (f:A -> B -> C) (a:eresult A) (b:eresult B) : eresult C :=
    lift_failure_in_two f a b.
  Definition elift3 {A B C D:Set} (f:A -> B -> C -> D)
             (a:eresult A) (b:eresult B) (c:eresult C) : eresult D :=
    lift_failure_in_three f a b c.
  Definition elift4 {A B C D E:Set} (f:A -> B -> C -> D -> E)
             (a:eresult A) (b:eresult B) (c:eresult C) (d:eresult D) : eresult E :=
    eolift (fun x => elift (fun g => g x) (elift3 f a b c)) d.
  Definition emaplift {A B:Set} (f:A -> eresult B) (al:list A) : eresult (list B) :=
    lift_failure_map f al.
  Definition eresult_of_option {A:Set} (a:option A) (e:eerror) :=
    result_of_option a e.
  Definition option_of_eresult {A:Set} (a:eresult A) : option A :=
    option_of_result a.

  (** Built-in errors *)
  Section Builtin.
    Definition not_in_contract_error {A} : eresult A :=
      efailure (CompilationError ("Cannot use 'contract' variable outside of a contract")).
    Definition not_in_clause_error {A} : eresult A :=
      efailure (CompilationError ("Cannot use 'clause' variable outside of a clause")).

    (* CTO errors *)
    Definition import_not_found {A} (import:string) : eresult A :=
      efailure (CompilationError ("Import not found: " ++ import)).
    Definition resolve_name_not_found {A} (namespace:string) (name_ref:string) : eresult A :=
      efailure (CompilationError ("Cannot resolve name '" ++ name_ref++ "' not found in CTO with namespace " ++ namespace)).
    Definition import_name_not_found {A} (namespace:string) (name_ref:string) : eresult A :=
      efailure (CompilationError ("Cannot import name '" ++ name_ref++ "' in CTO with namespace " ++ namespace)).
  
    Definition ergo_default_package : string := "org.accordproject.ergo".
    Definition ergo_default_error_local_name : string := "Error".
    Definition ergo_default_error_name : string :=
      ergo_default_package ++ "." ++ ergo_default_error_local_name.

    Definition enforce_error_content : ErgoData.data :=
      ErgoData.dbrand (ergo_default_error_name::nil)
                      (ErgoData.drec (("message"%string, ErgoData.dstring "Enforce condition failed")::nil)).

    Definition unresolved_name_error {A} : eresult A :=
      efailure (CompilationError ("Unresolved name")).

    
  End Builtin.

End EResult.
