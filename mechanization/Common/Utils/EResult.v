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

Require Import Ascii.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EProvenance.

Section EResult.
  Inductive eerror : Set :=
  | ESystemError : provenance -> string -> eerror
  | EParseError : provenance -> string -> eerror
  | ECompilationError : provenance -> string -> eerror
  | ETypeError : provenance -> string -> eerror
  | ERuntimeError : provenance -> string -> eerror.
  
  Definition eresult (A:Set) := Result A eerror.
  Definition esuccess {A:Set} (a:A) : eresult A :=
    Success A eerror a.
  Definition efailure {A:Set} (e:eerror) : eresult A :=
    Failure A eerror e.

  Section Lift.
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

    Definition elift_both {A B:Set} (f: A -> B) (g:eerror -> B) (a:eresult A) : B :=
      match a with
      | Success _ _ s => f s
      | Failure _ _ e => g e
      end.
    Definition elift_maybe {A:Set} (f: A -> option (eresult A)) (a:eresult A) : eresult A :=
      match elift f a with
      | Success _ _ (Some s) => s
      | Success _ _ None => a
      | Failure _ _ e => efailure e
      end.
    Definition eolift2 {A B C : Set} (f : A -> B -> eresult C) (a : eresult A) (b : eresult B) : eresult C :=
      match elift2 f a b with
      | Failure _ _ f => efailure f
      | Success _ _ s => s
      end.

    (* Fold-left over functions returning eresults *)
    Definition elift_fold_left {A:Set} {B:Set}
               (f : A -> B -> eresult A) (l:list B) (a:A) : eresult A :=
      let proc_one (acc:eresult A) (x:B)
          : eresult A :=
          eolift (fun acc => f acc x) acc
      in
      fold_left proc_one l (esuccess a).

    (* Variant of Fold-left for functions passing eresults with a context *)
    Definition elift_context_fold_left_alt {A:Set} {B:Set} {C:Set}
               (f : C -> A -> eresult (B * C)) (l:list A) (c:C) : eresult (list B * C) :=
      elift_fold_left
        (fun acc c =>
           elift (fun mc => ((fst acc)++((fst mc)::nil), snd mc)) (f (snd acc) c))
        l
        (nil, c).

    (* Variant of Fold-left for functions passing eresults with a context *)
    Definition elift_context_fold_left {A:Set} {B:Set} {C:Set}
               (f : C -> A -> eresult (B * C)) (l:list A) (c:C) : eresult (list B * C) :=
      elift_fold_left
        (fun acc c =>
           elift (fun mc => ((fst acc)++((fst mc)::nil), snd mc)) (f (snd acc) c))
        l
        (nil, c).

    Section qcert.
      Definition eerror_of_qerror (prov:provenance) (qe:qerror) :=
        match qe with
        | QResult.CompilationError msg => ECompilationError prov msg
        | QResult.TypeError msg => ETypeError prov msg
        | QResult.UserError msg =>  ESystemError prov "User error occured in backend"
        end.

      Definition eresult_of_qresult {A:Set} (prov:provenance) (a:qresult A) : eresult A :=
        match a with
        | Result.Success _ _ s => esuccess s
        | Result.Failure _ _ e => efailure (eerror_of_qerror prov e)
        end.

      Definition option_of_eresult {A:Set} (a:eresult A) : option A :=
        option_of_result a.

    End qcert.

  End Lift.

  (** Built-in errors *)
  Section Builtin.
    Definition clause_call_not_on_contract_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Cannot call a clause except on 'contract'").
    Definition use_contract_not_in_contract_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Cannot use 'contract' variable outside of a contract").
    Definition call_clause_not_in_contract_error {A} prov clname : eresult A :=
      efailure (ECompilationError prov ("Cannot call clause " ++ clname ++ " outside of a contract")).
    Definition not_in_clause_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Cannot use 'clause' variable outside of a clause").

    (* CTO errors *)
    Definition import_not_found_error {A} prov (import:string) : eresult A :=
      efailure (ECompilationError prov ("Import not found: " ++ import)).
    Definition type_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find type with name '" ++ ln ++ "'")).
    Definition variable_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find variable with name '" ++ ln ++ "'")).
    Definition function_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find function with name '" ++ ln ++ "'")).
    Definition contract_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find contract with name '" ++ ln ++ "'")).
    Definition import_name_not_found_error {A} prov (namespace:string) (name_ref:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot import name '" ++ name_ref++ "' in CTO with namespace " ++ namespace)).
  
    (** Main clause creation errors *)
    Definition main_parameter_mismatch_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Parameter mismatch during main creation").
    Definition main_at_least_one_parameter_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Cannot create main if not at least one parameter").
    Definition main_not_a_class_error {A} prov (cname:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot create main for non-class type "++cname)).
    
    (** Call errors *)
    Definition function_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (ECompilationError prov ("Function '" ++ fname ++ "' not found")).
    Definition eval_function_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (ERuntimeError prov ("Function '" ++ fname ++ "' not found during eval")).
    Definition clause_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (ECompilationError prov ("Clause '" ++ fname ++ "' not found")).
    Definition call_params_error {A} prov (fname:string) : eresult A :=
      efailure (ECompilationError prov ("Parameter mismatch when calling function '" ++ fname ++ "'")).

    (** Other runtime errors *)
    Definition eval_unary_op_error {A} prov (op:ErgoOps.Unary.op) : eresult A :=
      efailure (ERuntimeError prov "Unary operation failed.").
    Definition eval_binary_op_error {A} prov (op:ErgoOps.Binary.op) : eresult A :=
      efailure (ERuntimeError prov "Binary operation failed.").
    Definition eval_if_not_boolean_error {A} prov : eresult A :=
      efailure (ERuntimeError prov "'If' condition not boolean.").
    Definition eval_match_let_optional_not_on_option_error {A} prov : eresult A :=
      efailure (ERuntimeError prov "Matched LetOption without an option.").
    Definition eval_foreach_not_on_array_error {A} prov : eresult A :=
      efailure (ERuntimeError prov "Foreach needs to be called on an array").

    (** System errors *)
    Definition no_ergo_module_error {A} prov : eresult A :=
      efailure (ESystemError prov ("No input ergo found")).
    Definition built_in_function_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (ESystemError prov ("Built in function " ++ fname ++ " not found")).
    Definition built_in_function_without_body_error {A} prov (fname:string) : eresult A :=
      efailure (ESystemError prov ("Built in function " ++ fname ++ " does not have a body")).
    Definition TODO {A : Set} prov (feature:string) : eresult A :=
      efailure (ESystemError prov ("Feature " ++ feature ++ " not implemented.")%string).

    Definition ergo_default_package : string := "org.accordproject.ergo".
    Definition ergo_default_error_proval_name : string := "Error".
    Definition ergo_default_error_name : string :=
      ergo_default_package ++ "." ++ ergo_default_error_proval_name.

    Definition enforce_error_content : ErgoData.data :=
      ErgoData.dbrand (ergo_default_error_name::nil)
                      (ErgoData.drec (("message"%string, ErgoData.dstring "Enforce condition failed")::nil)).

    Definition unresolved_name_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Unresolved name").
    Definition should_have_one_contract_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Should have exactly one contract").

    Definition contract_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'contract' in Ergo Calculus").
    Definition clause_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'clause' in Ergo Calculus").
    Definition state_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'state' in Ergo Calculus").
    Definition complex_foreach_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should only have single loop foreach in Ergo Calculus").
    Definition function_not_inlined_error {A} prov fname : eresult A :=
      efailure (ESystemError prov ("Function " ++ fname ++ " did not get inlined")).
    Definition function_in_group_not_inlined_error {A} prov gname fname : eresult A :=
      efailure (ESystemError prov ("Clause " ++ fname ++ " in contract " ++ gname ++ " did not get inlined")).
  End Builtin.

  Section Fmt.
    Definition format_error (name : string) (prov : provenance) (msg : string) :=
      let loc := loc_of_provenance prov in
      (name ++ " at " ++ (string_of_location loc) ++ " '" ++ msg ++ "'")%string.
  End Fmt.
  
End EResult.
