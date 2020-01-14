open Assoc
open Bindings
open BrandRelation
open CoqLibAdd
open EquivDec
open ForeignType
open Lattice
open RType
open String0
open Sublist

val record_kind_rtype_join :
  record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a1)
  list -> record_kind

val rtype_meet_compatible_records_dec :
  record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a2)
  list -> bool

val record_kind_rtype_meet : record_kind -> record_kind -> record_kind

val rtype_join_UU2080_ :
  foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
  rtype_UU2080_

val rtype_meet_UU2080_ :
  foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
  rtype_UU2080_

val rtype_join : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val rtype_meet : foreign_type -> brand_relation -> rtype -> rtype -> rtype
