open BinInt
open Datatypes
open EquivDec
open List0

(** val float_eq : float -> float -> bool **)

let float_eq = (fun n1 n2 -> n1 = n2)

(** val float_eq_dec : float coq_EqDec **)

let float_eq_dec x y =
  if float_eq x y then true else false

(** val float_list_min : float list -> float **)

let float_list_min l =
  fold_right (fun x y -> min x y) Float.infinity l

(** val float_list_max : float list -> float **)

let float_list_max l =
  fold_right (fun x y -> max x y) Float.neg_infinity l

(** val float_list_sum : float list -> float **)

let float_list_sum l =
  fold_right (fun x y -> x +. y) 0. l

(** val float_list_arithmean : float list -> float **)

let float_list_arithmean l =
  let ll = length l in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> 0.)
     (fun _ ->
     (fun x y -> x /. y) (float_list_sum l)
       ((fun x -> float_of_int x) (Z.of_nat ll)))
     ll)
