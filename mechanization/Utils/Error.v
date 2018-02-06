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

Section Error.
  Section definition.
    Context (A: Type) (E: Type).

    Inductive Result : Type :=
    | Success : A -> Result
    | Failure : E -> Result.
  End definition.

  Section operations.
    Require Import List.

    Definition lift_error {A B E:Type} (f:A -> Result B E) : (Result A E -> Result B E) :=
      fun r =>
        match r with
        | Success _ _ a => f a
        | Failure _ _ e => Failure _ _ e
        end.

    Definition lift_error_in {A B E:Type} (f: A -> B) : (Result A E -> Result B E) :=
        fun r =>
          lift_error (fun a :A  => Success _ _ (f a)) r.

    Definition raise_error {A B E:Type} (f:A -> B) (e:E) : (Result A E -> Result B E) :=
      fun r =>
        Failure _ _ e.

    Definition lift_error_in_two {A B C E:Type} (f:A -> B -> C)
      : (Result A E -> Result B E -> Result C E) :=
      fun a =>
        match a with
        | Failure _ _ e => fun b => Failure _ _ e
        | Success _ _ a =>
          (fun b =>
             match b with
             | Failure _ _ e => Failure _ _ e
             | Success _ _ b =>
               Success _ _ (f a b)
             end)
        end.
    
    Definition lift_error_in_three {A B C D E:Type} (f:A -> B -> C -> D)
      : (Result A E -> Result B E -> Result C E -> Result D E) :=
      fun a =>
        match a with
        | Failure _ _ e => fun b => fun c => Failure _ _ e
        | Success _ _ a =>
          (fun b =>
             match b with
             | Failure _ _ e => fun c => Failure _ _ e
             | Success _ _ b =>
               (fun c =>
                  match c with
                  | Failure _ _ e => Failure _ _ e
                  | Success _ _ c  =>
                    Success _ _ (f a b c)
                  end)
             end)
        end.
    
    Fixpoint lift_error_map {A B E:Type} (f: A -> Result B E) (al:list A) : Result (list B) E :=
      let init_bl := Success _ _ nil in
      let proc_one (a:A) (acc:Result (list B) E) : Result (list B) E :=
          lift_error_in_two
            cons
            (f a)
            acc
      in
      fold_right proc_one init_bl al.

    Definition result_of_option {A E:Type} (a:option A) (e:E) : Result A E :=
      match a with
      | Some a => Success _ _ a
      | None => Failure _ _ e
      end.
  End operations.

  Section jura.
    Require Import String.

    Inductive jerror : Set :=
    | CompilationError : string -> jerror
    | ExecutionError : string -> jerror.

    Definition jresult (A:Set) := Result A jerror.
    Definition jsuccess {A:Set} (a:A) : jresult A :=
      Success A jerror a.
    Definition jfailure {A:Set} (e:jerror) : jresult A :=
      Failure A jerror e.
    Definition jolift {A B:Set} (f:A -> jresult B) (a:jresult A) : jresult B :=
      lift_error f a.
    Definition jlift {A B:Set} (f:A -> B) (a:jresult A) : jresult B :=
      lift_error_in f a.
    Definition jlift2 {A B C:Set} (f:A -> B -> C) (a:jresult A) (b:jresult B) : jresult C :=
      lift_error_in_two f a b.
    Definition jlift3 {A B C D:Set} (f:A -> B -> C ->D)
               (a:jresult A) (b:jresult B) (c:jresult C) : jresult D :=
      lift_error_in_three f a b c.
    Definition jmaplift {A B:Set} (f:A -> jresult B) (al:list A) : jresult (list B) :=
      lift_error_map f al.
    Definition jresult_of_option {A:Set} (a:option A) (e:jerror) :=
      result_of_option a e.
  End jura.

End Error.

