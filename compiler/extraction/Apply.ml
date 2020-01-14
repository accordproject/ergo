
(** val apply_unary : ('a1 -> 'a1 option) -> 'a1 list -> 'a1 option **)

let apply_unary f = function
| [] -> None
| d :: l -> (match l with
             | [] -> f d
             | _ :: _ -> None)

(** val apply_binary :
    ('a1 -> 'a1 -> 'a1 option) -> 'a1 list -> 'a1 option **)

let apply_binary f = function
| [] -> None
| d1 :: l ->
  (match l with
   | [] -> None
   | d2 :: l0 -> (match l0 with
                  | [] -> f d1 d2
                  | _ :: _ -> None))
