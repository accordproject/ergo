open Assoc
open CoqLibAdd
open ForeignType
open RType
open Sublist
open TBrandModel
open TSortBy
open TUtil

val tunrecsortable :
  foreign_type -> brand_model -> char list list -> rtype -> rtype option
