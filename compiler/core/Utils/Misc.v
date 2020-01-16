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

(** This file includes a few definitions and theorems used throughout the development *)

Require Import String.
Require Import List.
Require Import Qcert.Utils.NativeString.

Section Misc.
  Section String.
    Local Open Scope nstring_scope.
    Definition nstring_multi_append {A} separator (f:A -> nstring) (elems:list A) : nstring :=
      match elems with
      | nil => nstring_quote ""
      | e :: elems' =>
        (fold_left (fun acc e => acc +++ separator +++ (f e)) elems' (f e))%string
      end.

    (** Turns "foo.bar.baz" into "baz" if there is at least one '.' character *)
    Parameter get_local_part : string -> option string.

    (** Finds duplicates in a list of strings *)
    Parameter find_duplicate : list string -> option string.
  End String.

  Section List.
    Fixpoint filter_some {A B} (f:A -> option B) (l:list A) : list B :=
      match l with
      | nil => nil
      | x :: t =>
        match f x with
        | None => (filter_some f t)
        | Some x' => x' :: (filter_some f t)
        end
      end.

    Definition postpend {A} (ls : list A) (a : A) : list A :=
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

  End List.

  (** Topological sort. *)
  Section TopoSort.
    (* XXX It would be nice to be able to rely on a Coq library for
    this, but for now we assume a topological sort written in OCaml *)
    
    Context {A B C:Set}.
    (* function from node to node identifier -> function from node to label -> graph edges -> ordered nodes *)
    (* This assumes no two nodes have the same string *)
    Parameter coq_distinct : (A -> string) -> list A -> list A.
    Parameter coq_toposort : (A -> B) -> (A -> string) -> list (A * list A) -> list A.
    Parameter coq_sort_given_topo_order : list A -> (A -> string) -> (C-> string) -> (A -> string) -> list C -> list C.
  End TopoSort.

  (** Time monitoring *)
  Section TimeInstrumentation.
    Context {A B:Set}.
    Parameter coq_time : string -> (A -> B) -> A -> B.
  End TimeInstrumentation.

  (** Can printout warnings *)
  Section Warnings.
    Context {A:Set}.
    Parameter coq_print_warnings : string -> list string -> A -> A.
  End Warnings.
End Misc.

