open EquivDec
open List0

(** val coq_Forall_dec_defined : ('a1 -> bool) -> 'a1 list -> bool **)

let rec coq_Forall_dec_defined pdec = function
| [] -> true
| y :: l0 -> if coq_Forall_dec_defined pdec l0 then pdec y else false

(** val incl_list_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let incl_list_dec dec l1 l2 =
  if forallb (fun x -> if in_dec dec x l2 then true else false) l1
  then true
  else false

(** val coq_NoDup_dec : 'a1 coq_EqDec -> 'a1 list -> bool **)

let rec coq_NoDup_dec dec = function
| [] -> true
| y :: l0 ->
  let s = in_dec (equiv_dec dec) y l0 in
  if s then false else coq_NoDup_dec dec l0

(** val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option **)

let rec zip l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> Some []
           | _ :: _ -> None)
  | x1 :: l1' ->
    (match l2 with
     | [] -> None
     | x2 :: l2' ->
       (match zip l1' l2' with
        | Some l3 -> Some ((x1, x2) :: l3)
        | None -> None))
