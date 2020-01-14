open Datatypes
open Lift

(** val lift_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec lift_map f = function
| [] -> Some []
| x :: t ->
  (match f x with
   | Some x' -> lift (fun t' -> x' :: t') (lift_map f t)
   | None -> None)

(** val lift_flat_map :
    ('a1 -> 'a2 list option) -> 'a1 list -> 'a2 list option **)

let rec lift_flat_map f = function
| [] -> Some []
| x :: t ->
  (match f x with
   | Some x' -> lift (fun t' -> app x' t') (lift_flat_map f t)
   | None -> None)
