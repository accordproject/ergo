open Assoc
open Datatypes
open EquivDec
open List0

(** val compatible_with :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> 'a1 -> 'a2 -> ('a1 * 'a2) list -> bool **)

let compatible_with h1 h2 a b l_UU2082_ =
  match assoc_lookupr (equiv_dec h1) l_UU2082_ a with
  | Some d' -> if equiv_dec h2 b d' then true else false
  | None -> true

(** val compatible :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) list -> ('a1 * 'a2) list ->
    bool **)

let compatible h1 h2 l_UU2081_ l_UU2082_ =
  forallb (fun xy -> compatible_with h1 h2 (fst xy) (snd xy) l_UU2082_)
    l_UU2081_
