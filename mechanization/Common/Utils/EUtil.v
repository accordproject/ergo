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

Section EUtil.
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
    Context {A B:Set}.
    (* function from node to node identifier -> function from node to node name -> graph edges -> ordered nodes *)
    (* This assumes no two nodes have the same string *)
    Parameter coq_toposort : (A -> B) -> (A -> string) -> list (A * list A) -> list A.
  End TopoSort.
End EUtil.
