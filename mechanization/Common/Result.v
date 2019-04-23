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
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Ast.

Section Result.
  Inductive eerror : Set :=
  | ESystemError : provenance -> string -> eerror
  | EParseError : provenance -> string -> eerror
  | ECompilationError : provenance -> string -> eerror
  | ETypeError : provenance -> string -> eerror
  | ERuntimeError : provenance -> string -> eerror.

  Inductive ewarning : Set :=
  | EWarning : provenance -> string -> ewarning.

  Definition eresult (A:Set) := Result (A * list ewarning) eerror.
  Definition esuccess {A:Set} (a:A) (l:list ewarning) : eresult A :=
    Success (A * list ewarning) eerror (a,l).
  Definition efailure {A:Set} (e:eerror) : eresult A :=
    Failure (A * list ewarning) eerror e.

  Section Lift.
    Definition eolift {A B:Set} (f:A -> eresult B) (a:eresult A) : eresult B :=
      lift_failure
        (fun xw : (A * list ewarning) =>
           let (x,w) := xw in
           lift_failure_in
             (fun xw' : (B * list ewarning) =>
                let (x',w') := xw' in
                (x',w ++ w'))
             (f x)) a.

    Definition eolift_warning {A B:Set} (f:A * list ewarning -> eresult B) (a:eresult A) : eresult B :=
      lift_failure f a.

    Definition elift {A B:Set} (f:A -> B) (a:eresult A) : eresult B :=
      lift_failure_in
        (fun xw : (A * list ewarning) =>
           let (x,w) := xw in
           (f x, w)) a.
    Definition elift_warning {A B:Set} (f:A * list ewarning -> B) (a:eresult A) : eresult B :=
      lift_failure_in
        (fun xw : (A * list ewarning) =>
           (f xw, snd xw)) a.

    Definition elift2 {A B C:Set} (f:A -> B -> C) (a:eresult A) (b:eresult B) : eresult C :=
      eolift (fun x => elift (fun y => f x y) b) a.
    Definition elift3 {A B C D:Set} (f:A -> B -> C -> D)
               (a:eresult A) (b:eresult B) (c:eresult C) : eresult D :=
      eolift (fun x => elift2 (fun y z => f x y z) b c) a.
    Definition elift4 {A B C D E:Set} (f:A -> B -> C -> D -> E)
               (a:eresult A) (b:eresult B) (c:eresult C) (d:eresult D) : eresult E :=
      eolift (fun x => elift3 (fun y z xx => f x y z xx) b c d) a.
    Definition elift5 {A B C D E F:Set} (f:A -> B -> C -> D -> E -> F)
               (a:eresult A) (b:eresult B) (c:eresult C) (d:eresult D) (e:eresult E) : eresult F :=
      eolift (fun x => elift4 (fun y z xx yy => f x y z xx yy) b c d e) a.

    (* Fold-left over functions returning eresults *)
    Definition elift_fold_left {A:Set} {B:Set}
               (f : A -> B -> eresult A) (l:list B) (a:A) : eresult A :=
      let proc_one (acc:eresult A) (x:B)
          : eresult A :=
          eolift (fun acc => f acc x) acc
      in
      fold_left proc_one l (esuccess a nil).

    (* Map over functions returning eresults *)
    Definition emaplift {A B:Set} (f:A -> eresult B) (al:list A) : eresult (list B) :=
      let init_bl := Success (list B * list ewarning) _ (nil, nil) in
      let proc_one := fun (acc : eresult (list B)) (a : A) => elift2 (fun acc x => app acc (x::nil)) acc (f a) in
      fold_left proc_one al init_bl.

    (* Variant of Fold-left for functions passing eresults with a context *)
    Definition elift_context_fold_left {A:Set} {B:Set} {C:Set}
               (f : C -> A -> eresult (B * C)) (l:list A) (c:C) : eresult (list B * C) :=
      elift_fold_left
        (fun acc c =>
           elift (fun mc => ((fst acc)++((fst mc)::nil), snd mc)) (f (snd acc) c))
        l
        (nil, c).

    Definition eflatmaplift {A B:Set} (f:A -> eresult (list B)) (al:list A) : eresult (list B) :=
      elift_fold_left
        (fun acc c =>
           elift (fun mc => acc ++ mc) (f c))
        al nil.

    Definition eresult_of_option {A:Set} (a:option A) (e:eerror) (warnings:list ewarning) : eresult A :=
      result_of_option (lift (fun x => (x,warnings)) a) e.

    Definition eolift2 {A B C:Set} (f : A -> B -> eresult C) (a : eresult A) (b : eresult B) : eresult C :=
      eolift id (elift2 f a b).
     
    Definition elift_maybe {A:Set} (f: A -> option (eresult A)) (a:eresult A) : eresult A :=
      eolift
        (fun x =>
           match x with
           | None => a
           | Some s => s
           end)
        (elift f a).

    (* XXX Those lose warnings *)
    Definition elift_both {A B:Set} (f: A -> B) (g:eerror -> B) (a:eresult A) : B :=
      match a with
      | Success _ _ (s,_) => f s
      | Failure _ _ e => g e
      end.
    Definition elift2_both {A B C:Set} (f: A -> B -> C) (g:eerror -> C) (a:eresult A) (b:eresult B) : C :=
      match a with
      | Success _ _ (s1,_) =>
        match b with
        | Success _ _ (s2,_) => f s1 s2
        | Failure _ _ e => g e
        end
      | Failure _ _ e => g e
      end.

    Section qcert.
      Definition eerror_of_qerror (prov:provenance) (qe:qerror) :=
        match qe with
        | QResult.CompilationError msg => ECompilationError prov msg
        | QResult.TypeError msg => ETypeError prov msg
        | QResult.UserError msg =>  ESystemError prov "User error occured in backend"
        end.

      Definition eresult_of_qresult {A:Set} (prov:provenance) (a:qresult A) : eresult A :=
        match a with
        | Result.Success _ _ s => esuccess s nil
        | Result.Failure _ _ e => efailure (eerror_of_qerror prov e)
        end.

      Definition option_of_eresult {A:Set} (a:eresult A) : option A :=
        lift fst (option_of_result a).

    End qcert.

  End Lift.

  Section Fmt.
    Definition format_error (name : string) (prov : provenance) (msg : string) : string :=
      let loc := loc_of_provenance prov in
      (name ++ " at " ++ (string_of_location_no_file loc) ++ " '" ++ msg ++ "'")%string.
  End Fmt.
  
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
    Definition case_option_not_on_either_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Cannot match unless against an option type").

    (* CTO errors *)
    Definition import_not_found_error {A} prov (import:string) : eresult A :=
      efailure (ECompilationError prov ("Import not found: " ++ import)).
    Definition type_name_not_found_error {A} prov (ln:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find type with name '" ++ ln ++ "'")).
    Definition namespace_not_found_error {A} prov (ns:string) : eresult A :=
      efailure (ECompilationError prov ("Cannot find namespace '" ++ ns ++ "'")).
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
    Definition clause_not_found_error {A} prov (fname:string) : eresult A :=
      efailure (ECompilationError prov ("Clause '" ++ fname ++ "' not found")).
    Definition call_params_error {A} prov (fname:string) : eresult A :=
      efailure (ECompilationError prov ("Parameter mismatch when calling function '" ++ fname ++ "'")).

    (** Other runtime errors *)
    Definition eval_unary_operator_error {A} prov (op:ergo_unary_operator) : eresult A :=
      let op_name := toString op in
      efailure (ESystemError prov ("Unexpected operator [" ++ op_name ++ "] during eval (should have been resolved).")).
    Definition eval_binary_operator_error {A} prov (op:ergo_binary_operator) : eresult A :=
      let op_name := toString op in
      efailure (ESystemError prov ("Unexpected operator [" ++ op_name ++ "] during eval (should have been resolved).")).
    Definition eval_unary_builtin_error {A} prov (op:ErgoOps.Unary.op) : eresult A :=
      let op_name := toString op in
      efailure (ERuntimeError prov ("Evaluation for builtin unary operator [" ++ op_name ++ "] failed.")).
    Definition eval_binary_builtin_error {A} prov (op:ErgoOps.Binary.op) : eresult A :=
      let op_name := toString op in
      efailure (ERuntimeError prov ("Evaluation for builtin binary operator [" ++ op_name ++ "] failed.")).
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

    Definition enforce_error_content (prov:provenance) (msg:string) : ErgoData.data :=
      let message := format_error "Enforce Error" prov msg in
      ErgoData.dbrand (default_error_absolute_name::nil)
                      (ErgoData.drec (("message"%string, ErgoData.dstring message)::nil)).
    Definition default_match_error_content (prov:provenance) : ErgoData.data :=
      let message := "Dispatch Error: no clause in the contract matches the request"%string in
      ErgoData.dbrand (default_error_absolute_name::nil)
                      (ErgoData.drec (("message"%string, ErgoData.dstring message)::nil)).

    Definition unresolved_name_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Unresolved name").
    Definition should_have_one_contract_error {A} prov : eresult A :=
      efailure (ECompilationError prov "Should have exactly one contract").

    Definition contract_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'contract' in Ergo Calculus").
    Definition clause_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'clause' in Ergo Calculus").
    Definition operator_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find an overloaded operator in Ergo Calculus").
    Definition state_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'state' in Ergo Calculus").
    Definition text_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find '{{ text }}' in Ergo Calculus").
    Definition complex_foreach_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should only have single loop foreach in Ergo Calculus").
    Definition print_in_calculus_error {A} prov : eresult A :=
      efailure (ESystemError prov "Should not find 'print' in Ergo Calculus").
    Definition function_not_inlined_error {A} prov msg fname : eresult A :=
      efailure (ESystemError prov ("[" ++ msg ++ "] " ++ "Function " ++ fname ++ " did not get inlined")).
    Definition function_in_group_not_inlined_error {A} prov gname fname : eresult A :=
      efailure (ESystemError prov ("Clause " ++ fname ++ " in contract " ++ gname ++ " did not get inlined")).
  End Builtin.

  Section Duplicates.
    Context {A:Set}.
    Definition no_duplicates_with_err
               (l:list string)
               (succ:A)
               (err:option string -> eerror) : eresult A :=
      if (@NoDup_dec string string_dec l)
      then esuccess succ nil
      else
        let s := find_duplicate l in
        efailure (err s).

    Definition duplicate_function_params_error prov (fname:string) (vname:option string) : eerror :=
      match vname with
      | None =>
        ECompilationError prov ("Same variable bound multiple times in '" ++ fname ++ "'")
      | Some vname =>
        ECompilationError prov ("Variable '" ++ vname ++ "' is bound multiple times in '" ++ fname ++ "'")
      end.
    Definition duplicate_function_params_check prov (fname:string) (l:list string) (succ:A) : eresult A :=
      no_duplicates_with_err l succ (duplicate_function_params_error prov fname).

    Definition duplicate_clause_for_request_error prov (rname:option string) : eerror :=
      match rname with
      | None =>
        ECompilationError prov ("Multiple clauses can process the same request")
      | Some rname =>
        ECompilationError prov ("Multiple clauses can process the request '" ++ rname ++ "'")
      end.
    Definition duplicate_clause_for_request_check prov (l:list string) (succ:A) : eresult A :=
      no_duplicates_with_err l succ (duplicate_clause_for_request_error prov).
  End Duplicates.


  Section warnings.
    Definition string_of_warning (w:ewarning) : string :=
      match w with
      | EWarning prov msg => msg
      end.
    Definition print_warnings {A:Set} (prefix:string) (x:eresult A) : eresult A :=
      elift_warning (fun xy => coq_print_warnings prefix (List.map string_of_warning (snd xy)) (fst xy)) x.
  End warnings.
End Result.
