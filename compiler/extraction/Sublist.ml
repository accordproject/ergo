open EquivDec

(** val sublist_dec : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> bool **)

let rec sublist_dec dec l1 = function
| [] -> (match l1 with
         | [] -> true
         | _ :: _ -> false)
| y :: l ->
  (match l1 with
   | [] -> true
   | a0 :: l3 ->
     let s = equiv_dec dec a0 y in
     if s then sublist_dec dec l3 l else sublist_dec dec (a0 :: l3) l)
