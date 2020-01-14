
(** val insertion_sort_insert :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insertion_sort_insert r_dec a = function
| [] -> a :: []
| b :: xs ->
  if r_dec a b
  then a :: (b :: xs)
  else if r_dec b a then b :: (insertion_sort_insert r_dec a xs) else b :: xs

(** val insertion_sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec insertion_sort r_dec = function
| [] -> []
| a :: xs -> insertion_sort_insert r_dec a (insertion_sort r_dec xs)

(** val is_list_sorted : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec is_list_sorted r_dec = function
| [] -> true
| x :: xs ->
  (match xs with
   | [] -> true
   | y :: _ -> if r_dec x y then is_list_sorted r_dec xs else false)
