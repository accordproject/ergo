
type ('a, 'e) coq_Result =
| Success of 'a
| Failure of 'e

(** val lift_failure :
    ('a1 -> ('a2, 'a3) coq_Result) -> ('a1, 'a3) coq_Result -> ('a2, 'a3)
    coq_Result **)

let lift_failure f = function
| Success a -> f a
| Failure e -> Failure e

(** val lift_failure_in :
    ('a1 -> 'a2) -> ('a1, 'a3) coq_Result -> ('a2, 'a3) coq_Result **)

let lift_failure_in f r =
  lift_failure (fun a -> Success (f a)) r

(** val result_of_option : 'a1 option -> 'a2 -> ('a1, 'a2) coq_Result **)

let result_of_option a e =
  match a with
  | Some a0 -> Success a0
  | None -> Failure e
