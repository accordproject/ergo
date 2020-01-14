open Assoc
open Bindings
open BrandRelation
open CoqLibAdd
open Datatypes
open EquivDec
open ForeignType
open List0
open SortingAdd
open String0

type record_kind =
| Open
| Closed

val record_kind_eqdec : record_kind coq_EqDec

type rtype_UU2080_ =
| Bottom_UU2080_
| Top_UU2080_
| Unit_UU2080_
| Nat_UU2080_
| Float_UU2080_
| Bool_UU2080_
| String_UU2080_
| Coll_UU2080_ of rtype_UU2080_
| Rec_UU2080_ of record_kind * (char list * rtype_UU2080_) list
| Either_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Arrow_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Brand_UU2080_ of brands
| Foreign_UU2080_ of foreign_type_type

val rtype_UU2080__eqdec : foreign_type -> rtype_UU2080_ coq_EqDec

type rtype = rtype_UU2080_

val rtype_eq_dec : foreign_type -> brand_relation -> rtype coq_EqDec

val coq_Bottom : foreign_type -> brand_relation -> rtype

val coq_Top : foreign_type -> brand_relation -> rtype

val coq_Unit : foreign_type -> brand_relation -> rtype

val coq_Nat : foreign_type -> brand_relation -> rtype

val coq_Float : foreign_type -> brand_relation -> rtype

val coq_Bool : foreign_type -> brand_relation -> rtype

val coq_String : foreign_type -> brand_relation -> rtype

val coq_Coll : foreign_type -> brand_relation -> rtype -> rtype

val coq_Either : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val coq_Arrow : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val coq_Foreign : foreign_type -> brand_relation -> foreign_type_type -> rtype

val coq_Rec :
  foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
  -> rtype

val coq_Brand : foreign_type -> brand_relation -> brands -> rtype

val coq_Option : foreign_type -> brand_relation -> rtype -> rtype

val from_Rec_UU2080_ :
  foreign_type -> brand_relation -> record_kind ->
  (char list * rtype_UU2080_) list -> (char list * rtype_UU2080_) list

val coq_RecMaybe :
  foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
  -> rtype option
