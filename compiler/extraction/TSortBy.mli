open Bindings
open ForeignType
open ListAdd
open RType
open TBrandModel

val sortable_type_dec : foreign_type -> brand_model -> rtype -> bool

val order_by_has_sortable_type_dec :
  foreign_type -> brand_model -> (char list * rtype) list -> char list list
  -> bool
