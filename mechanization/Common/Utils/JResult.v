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
Require Import Jura.Backend.JuraBackend.

Section JResult.
  Inductive jerror : Set :=
  | CompilationError : string -> jerror
  | TypeError : string -> jerror
  | UserError : JuraData.data -> jerror.

  Definition jresult (A:Set) := Result A jerror.
  Definition jsuccess {A:Set} (a:A) : jresult A :=
    Success A jerror a.
  Definition jfailure {A:Set} (e:jerror) : jresult A :=
    Failure A jerror e.
  Definition jolift {A B:Set} (f:A -> jresult B) (a:jresult A) : jresult B :=
    lift_failure f a.
  Definition jlift {A B:Set} (f:A -> B) (a:jresult A) : jresult B :=
    lift_failure_in f a.
  Definition jlift2 {A B C:Set} (f:A -> B -> C) (a:jresult A) (b:jresult B) : jresult C :=
    lift_failure_in_two f a b.
  Definition jlift3 {A B C D:Set} (f:A -> B -> C ->D)
             (a:jresult A) (b:jresult B) (c:jresult C) : jresult D :=
    lift_failure_in_three f a b c.
  Definition jmaplift {A B:Set} (f:A -> jresult B) (al:list A) : jresult (list B) :=
    lift_failure_map f al.
  Definition jresult_of_option {A:Set} (a:option A) (e:jerror) :=
    result_of_option a e.
  Definition option_of_jresult {A:Set} (a:jresult A) : option A :=
    option_of_result a.
End JResult.

