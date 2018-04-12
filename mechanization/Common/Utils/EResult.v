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
Require Import Qcert.Utils.Result.
Require Import ErgoSpec.Backend.ErgoBackend.

Section EResult.
  Inductive eerror : Set :=
  | CompilationError : string -> eerror
  | TypeError : string -> eerror
  | UserError : ErgoData.data -> eerror.

  Definition eresult (A:Set) := Result A eerror.
  Definition esuccess {A:Set} (a:A) : eresult A :=
    Success A eerror a.
  Definition efailure {A:Set} (e:eerror) : eresult A :=
    Failure A eerror e.
  Definition jolift {A B:Set} (f:A -> eresult B) (a:eresult A) : eresult B :=
    lift_failure f a.
  Definition jlift {A B:Set} (f:A -> B) (a:eresult A) : eresult B :=
    lift_failure_in f a.
  Definition jlift2 {A B C:Set} (f:A -> B -> C) (a:eresult A) (b:eresult B) : eresult C :=
    lift_failure_in_two f a b.
  Definition jlift3 {A B C D:Set} (f:A -> B -> C ->D)
             (a:eresult A) (b:eresult B) (c:eresult C) : eresult D :=
    lift_failure_in_three f a b c.
  Definition jmaplift {A B:Set} (f:A -> eresult B) (al:list A) : eresult (list B) :=
    lift_failure_map f al.
  Definition eresult_of_option {A:Set} (a:option A) (e:eerror) :=
    result_of_option a e.
  Definition option_of_eresult {A:Set} (a:eresult A) : option A :=
    option_of_result a.
End EResult.

