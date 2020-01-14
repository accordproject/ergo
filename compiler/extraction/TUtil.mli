open Assoc
open Bindings
open CoqLibAdd
open ForeignType
open RType
open Sublist
open TBrandModel

val tdot : (char list * 'a1) list -> char list -> 'a1 option

val tuneither : foreign_type -> brand_model -> rtype -> (rtype * rtype) option

val tuncoll : foreign_type -> brand_model -> rtype -> rtype option

val tsingleton : foreign_type -> brand_model -> rtype -> rtype option

val tunrec :
  foreign_type -> brand_model -> rtype -> (record_kind * (char list * rtype)
  list) option

val trecConcatRight :
  foreign_type -> brand_model -> rtype -> rtype -> rtype option

val tmergeConcat :
  foreign_type -> brand_model -> rtype -> rtype -> rtype option

val tunrecdot :
  foreign_type -> brand_model -> char list -> rtype -> rtype option

val tunrecremove :
  foreign_type -> brand_model -> char list -> rtype -> rtype option

val tunrecproject :
  foreign_type -> brand_model -> char list list -> rtype -> rtype option
