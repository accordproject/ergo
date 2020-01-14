open Assoc
open CoqLibAdd
open ForeignType
open RType
open Sublist
open TBrandModel
open TSortBy
open TUtil

(** val tunrecsortable :
    foreign_type -> brand_model -> char list list -> rtype -> rtype option **)

let tunrecsortable ftype m sl _UU03c4_ =
  match tunrec ftype m _UU03c4_ with
  | Some p ->
    let (_, l) = p in
    let s = sublist_dec string_eqdec sl (domain l) in
    if s
    then let s0 = order_by_has_sortable_type_dec ftype m l sl in
         if s0 then Some _UU03c4_ else None
    else None
  | None -> None
