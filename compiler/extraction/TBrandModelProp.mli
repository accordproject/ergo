open Assoc
open BrandRelation
open ForeignType
open Lattice
open List0
open RType
open RTypeLattice
open String0
open TBrandContext
open TBrandModel

val brands_type_list : foreign_type -> brand_model -> brands -> rtype list

val brands_type : foreign_type -> brand_model -> brands -> rtype
