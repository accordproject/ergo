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
Require Import ZArith.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EProvenance.

Section EResult.
  Inductive eerror : Set :=
  | SystemError : provenance -> string -> eerror
  | ParseError : provenance -> string -> eerror
  | CompilationError : provenance -> string -> eerror
  | TypeError : provenance -> string -> eerror
  | RuntimeError : provenance -> string -> eerror.

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
  Definition elift5 {A B C D E F:Set} (f:A -> B -> C -> D -> E -> F)
             (a:eresult A) (b:eresult B) (c:eresult C) (d:eresult D) (e:eresult E) : eresult F :=
    eolift (fun x => elift (fun g => g x) (elift4 f a b c d)) e.
  Definition emaplift {A B:Set} (f:A -> eresult B) (al:list A) : eresult (list B) :=
    lift_failure_map f al.
  Definition eresult_of_option {A:Set} (a:option A) (e:eerror) :=
    result_of_option a e.
  Definition option_of_eresult {A:Set} (a:eresult A) : option A :=
    option_of_result a.

  (* Fold-left over functions returning eresults *)
  Definition elift_fold_left {A:Set} {B:Set}
             (f : A -> B -> eresult A) (l:list B) (a:A) : eresult A :=
    let proc_one (acc:eresult A) (x:B)
        : eresult A :=
        eolift (fun acc => f acc x) acc
    in
    fold_left proc_one l (esuccess a).

  (* Variant of Fold-left for functions passing eresults with a context *)
  Definition elift_context_fold_left {A:Set} {B:Set} {C:Set}
             (f : C -> A -> eresult (B * C)) (l:list A) (c:C) : eresult (list B * C) :=
    elift_fold_left
      (fun acc c =>
         elift (fun mc => ((fst acc)++((fst mc)::nil), snd mc)) (f (snd acc) c))
      l
      (nil, c).

  (** Built-in errors *)
  Section Builtin.

    Definition not_in_contract_error {A} prov : eresult A :=
      efailure (CompilationError prov "Cannot use 'contract' variable outside of a contract").
    Definition not_in_clause_error {A} prov : eresult A :=
      efailure (CompilationError prov "Cannot use 'clause' variable outside of a clause").

    Definition TODO {A : Set} : eresult A :=
        efailure (SystemError dummy_provenance "Feature not implemented."%string).

    (* CTO errors *)
    Definition import_not_found_error {A} prov (import:string) : eresult A :=
      efailure (CompilationError prov ("Import not found: " ++ import)).
    Definition type_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (CompilationError prov ("Cannot find type with name '" ++ ln ++ "'")).
    Definition variable_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (CompilationError prov ("Cannot find variable with name '" ++ ln ++ "'")).
    Definition function_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (CompilationError prov ("Cannot find function with name '" ++ ln ++ "'")).
    Definition import_name_not_found_error {A} prov (namespace:string) (name_ref:string) : eresult A :=
      efailure (CompilationError prov ("Cannot import name '" ++ name_ref++ "' in CTO with namespace " ++ namespace)).
  
    (** Main clause creation errors *)
    Definition main_parameter_mismatch_error {A} prov : eresult A :=
      efailure (CompilationError prov "Parameter mismatch during main creation").
    Definition main_at_least_one_parameter_error {A} prov : eresult A :=
      efailure (CompilationError prov "Cannot create main if not at least one parameter").
    Definition main_not_a_class_error {A} prov (cname:string) : eresult A :=
      efailure (CompilationError prov ("Cannot create main for non-class type "++cname)).
    
    (** Call errors *)
    Definition function_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (CompilationError prov ("Function '" ++ fname ++ "' not found")).
    Definition clause_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (CompilationError prov ("Clause '" ++ fname ++ "' not found")).
    Definition call_params_error {A} prov (fname:string) : eresult A :=
      efailure (CompilationError prov ("Parameter mismatch when calling function '" ++ fname ++ "'")).

    Definition ergo_default_package : string := "org.accordproject.ergo".
    Definition ergo_default_error_proval_name : string := "Error".
    Definition ergo_default_error_name : string :=
      ergo_default_package ++ "." ++ ergo_default_error_proval_name.

    Definition enforce_error_content : ErgoData.data :=
      ErgoData.dbrand (ergo_default_error_name::nil)
                      (ErgoData.drec (("message"%string, ErgoData.dstring "Enforce condition failed")::nil)).

    Definition unresolved_name_error {A} prov : eresult A :=
      efailure (CompilationError prov "Unresolved name").
    Definition should_have_one_contract_error {A} prov : eresult A :=
      efailure (CompilationError prov "Should have exactly one contract").

    Definition contract_in_calculus_error {A} prov : eresult A :=
      efailure (SystemError prov "Should not find 'contract' in Ergo Calculus").
    Definition clause_in_calculus_error {A} prov : eresult A :=
      efailure (SystemError prov "Should not find 'clause' in Ergo Calculus").
    Definition state_in_calculus_error {A} prov : eresult A :=
      efailure (SystemError prov "Should not find 'state' in Ergo Calculus").
    Definition complex_foreach_in_calculus_error {A} prov : eresult A :=
      efailure (SystemError prov "Should only have single loop foreach in Ergo Calculus").
  End Builtin.

End EResult.
