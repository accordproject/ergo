open Datatypes
open List0

(** val lookup :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option **)

let rec lookup dec l a =
  match l with
  | [] -> None
  | y :: os ->
    let (f', v') = y in if dec a f' then Some v' else lookup dec os a

(** val update_first :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 -> ('a1 * 'a2) list **)

let rec update_first dec l a n =
  match l with
  | [] -> []
  | y :: os ->
    let (f', v') = y in
    if dec a f' then (a, n) :: os else (f', v') :: (update_first dec os a n)

(** val domain : ('a1 * 'a2) list -> 'a1 list **)

let domain l =
  map fst l

(** val assoc_lookupr :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option **)

let rec assoc_lookupr eqd l a =
  match l with
  | [] -> None
  | p :: r2 ->
    let (a', d) = p in
    (match assoc_lookupr eqd r2 a with
     | Some d' -> Some d'
     | None -> if eqd a a' then Some d else None)

(** val lookup_diff :
    ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> ('a1 * 'a3) list ->
    ('a1 * 'a2) list **)

let rec lookup_diff dec l_UU2081_ l_UU2082_ =
  match l_UU2081_ with
  | [] -> []
  | x :: xs ->
    (match lookup dec l_UU2082_ (fst x) with
     | Some _ -> lookup_diff dec xs l_UU2082_
     | None -> x :: (lookup_diff dec xs l_UU2082_))
