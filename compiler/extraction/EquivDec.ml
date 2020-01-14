
type 'a coq_EqDec = 'a -> 'a -> bool

(** val equiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let equiv_dec eqDec =
  eqDec

(** val equiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let equiv_decb h x y =
  if equiv_dec h x y then true else false

(** val nat_eq_eqdec : int coq_EqDec **)

let nat_eq_eqdec =
  (=)

(** val unit_eqdec : unit coq_EqDec **)

let unit_eqdec _ _ =
  true

(** val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec **)

let rec list_eqdec eqa x y =
  match x with
  | [] -> (match y with
           | [] -> true
           | _ :: _ -> false)
  | hd :: tl ->
    (match y with
     | [] -> false
     | hd' :: tl' ->
       if equiv_dec eqa hd hd' then list_eqdec eqa tl tl' else false)
