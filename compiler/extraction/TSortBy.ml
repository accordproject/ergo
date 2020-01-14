open Bindings
open ForeignType
open ListAdd
open RType
open TBrandModel

(** val sortable_type_dec : foreign_type -> brand_model -> rtype -> bool **)

let sortable_type_dec _ _ = function
| Nat_UU2080_ -> true
| String_UU2080_ -> true
| _ -> false

(** val order_by_has_sortable_type_dec :
    foreign_type -> brand_model -> (char list * rtype) list -> char list list
    -> bool **)

let order_by_has_sortable_type_dec ftype m _UU03c4_r satts =
  coq_Forall_dec_defined (fun x ->
    match edot _UU03c4_r x with
    | Some r -> sortable_type_dec ftype m r
    | None -> true) satts
