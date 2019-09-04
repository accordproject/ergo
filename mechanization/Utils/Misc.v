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
Require Import List.

Section Misc.
  Definition multi_append {A} separator (f:A -> string) (elems:list A) : string :=
    match elems with
    | nil => ""
    | e :: elems' =>
      (fold_left (fun acc e => acc ++ separator ++ (f e)) elems' (f e))%string
    end.

  Fixpoint filter_some {A B:Type} (f:A -> option B) (l:list A) : list B :=
    match l with
    | nil => nil
    | x :: t =>
      match f x with
      | None => (filter_some f t)
      | Some x' => x' :: (filter_some f t)
      end
    end.

  Definition postpend {A : Set} (ls : list A) (a : A) : list A :=
    ls ++ (a :: nil).

  Fixpoint last_some {A} (l:list (option A)) : option A :=
    let proc_one (one:option A) (acc:option A) :=
        match acc with
        | Some x => Some x
        | None => one
        end
    in
    fold_right
      proc_one
      None
      l.

  Fixpoint last_some_pair {A} {B} (l:list ((option A) * (option B))) : ((option A) * (option B)) :=
    let proc_one (one : ((option A) * (option B))) (acc : ((option A) * (option B))) :=
        match acc with
        | (Some x, Some y) => acc
        | _ => one
        end
    in
    fold_right
      proc_one
      (None, None)
      l.

  Section TopoSort.
    Context {A B C:Set}.
    (* function from node to node identifier -> function from node to label -> graph edges -> ordered nodes *)
    (* This assumes no two nodes have the same string *)
    Parameter coq_distinct : (A -> string) -> list A -> list A.
    Parameter coq_toposort : (A -> B) -> (A -> string) -> list (A * list A) -> list A.
    Parameter coq_sort_given_topo_order : list A -> (A -> string) -> (C-> string) -> (A -> string) -> list C -> list C.
  End TopoSort.

  Section TimeInstrumentation.
    Context {A B:Set}.
    Parameter coq_time : string -> (A -> B) -> A -> B.
  End TimeInstrumentation.

  Section StringStuff.
    (** Turns "foo.bar.baz" into "baz" if there is at least on '.' character *)
    Parameter get_local_part : string -> option string.
  End StringStuff.

  Section Config.
    Inductive jsversion :=
    | ES5 : jsversion
    | ES6 : jsversion.
  End Config.

  Section EString.
    Parameter estring : Set.
    Parameter string_to_estring : string -> estring.
    Parameter estring_to_string : estring -> string.
    Parameter estring_concat : estring -> estring -> estring.

    Notation "` e" := (string_to_estring e) (left associativity, at level 40) : estring_scope.
    Notation "^ e" := (estring_to_string e) (left associativity, at level 40) : estring_scope.
    Notation "e1 +++ e2" := (estring_concat e1 e2) (right associativity, at level 70): estring_scope.

    Local Open Scope estring_scope.
    Definition emulti_append {A} separator (f:A -> estring) (elems:list A) : estring :=
      match elems with
      | nil => ` (""%string)
      | e :: elems' => fold_left (fun acc e => acc +++ separator +++ (f e)) elems' (f e)
      end.

    Fixpoint econcat (sep : estring) (ls : list estring) : estring :=
      match ls with
      | nil => `""%string
      | x :: nil => x
      | x :: (_ :: _) as xs => (x +++ sep +++ econcat sep xs)%string
      end.
    
    Definition ejavascript : Set := estring.

    Parameter flat_map_estring : (Ascii.ascii->estring) -> (estring) -> estring.
  End EString.

  Section Duplicates.
    Parameter find_duplicate : list string -> option string.
  End Duplicates.

  Section Warnings.
    Context {A:Set}.
    Parameter coq_print_warnings : string -> list string -> A -> A.
  End Warnings.
End Misc.

Notation "` e" := (string_to_estring e) (left associativity, at level 40) : estring_scope.
Notation "^ e" := (estring_to_string e) (left associativity, at level 40) : estring_scope.
Notation "e1 +++ e2" := (estring_concat e1 e2) (right associativity, at level 70): estring_scope.
