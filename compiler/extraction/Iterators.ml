open Data
open ForeignData
open LiftIterators

(** val oflatten : foreign_data -> data list -> data list option **)

let oflatten _ d =
  lift_flat_map (fun x -> match x with
                          | Coq_dcoll y -> Some y
                          | _ -> None) d
