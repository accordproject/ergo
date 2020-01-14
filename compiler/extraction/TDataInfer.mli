open BrandRelation
open Data
open ForeignData
open ForeignDataTyping
open ForeignType
open Lattice
open Lift
open RSubtype
open RType
open RTypeLattice
open TBrandModel
open TBrandModelProp

val infer_data_type :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model -> data
  -> rtype option
