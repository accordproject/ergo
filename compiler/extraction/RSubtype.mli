open Assoc
open BrandRelation
open CoqLibAdd
open Datatypes
open ForeignType
open List0
open ListAdd
open RType
open String0

val subtype_both_dec :
  foreign_type -> brand_relation -> rtype -> rtype -> bool * bool

val subtype_dec : foreign_type -> brand_relation -> rtype -> rtype -> bool

val check_subtype_pairs :
  foreign_type -> brand_relation -> (rtype * rtype) list -> bool

val enforce_unary_op_schema :
  foreign_type -> brand_relation -> (rtype * rtype) -> rtype ->
  (rtype * rtype) option

val enforce_binary_op_schema :
  foreign_type -> brand_relation -> (rtype * rtype) -> (rtype * rtype) ->
  rtype -> ((rtype * rtype) * rtype) option
