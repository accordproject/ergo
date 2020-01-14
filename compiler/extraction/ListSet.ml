
type 'a set = 'a list

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| [] -> false
| a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x y =
  match x with
  | [] -> []
  | a1 :: x1 ->
    if set_mem aeq_dec a1 y
    then a1 :: (set_inter aeq_dec x1 y)
    else set_inter aeq_dec x1 y
