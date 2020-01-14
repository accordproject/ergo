
type ('a, 'e) coq_Result =
| Success of 'a
| Failure of 'e

val lift_failure :
  ('a1 -> ('a2, 'a3) coq_Result) -> ('a1, 'a3) coq_Result -> ('a2, 'a3)
  coq_Result

val lift_failure_in :
  ('a1 -> 'a2) -> ('a1, 'a3) coq_Result -> ('a2, 'a3) coq_Result

val result_of_option : 'a1 option -> 'a2 -> ('a1, 'a2) coq_Result
