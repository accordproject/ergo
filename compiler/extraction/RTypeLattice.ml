open BrandRelation
open ForeignType
open Lattice
open RType
open RTypeMeetJoin

(** val rtype_lattice :
    foreign_type -> brand_relation -> rtype coq_Lattice **)

let rtype_lattice ftype br =
  { meet = (rtype_meet ftype br); join = (rtype_join ftype br) }
