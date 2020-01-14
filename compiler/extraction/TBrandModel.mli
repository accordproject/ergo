open Assoc
open BrandRelation
open Datatypes
open ForeignType
open List0
open ListAdd
open RSubtype
open String0
open TBrandContext

val brand_model_domain_dec :
  foreign_type -> brand_relation -> brand_context -> bool

val brand_model_subtype_weak_dec :
  foreign_type -> brand_relation -> brand_context -> bool

type brand_model = { brand_model_relation : brand_relation;
                     brand_model_context : brand_context }

val make_brand_model :
  foreign_type -> brand_relation -> brand_context -> brand_model

val empty_brand_model : foreign_type -> brand_model
