open Bindings
open BrandRelation
open CoqLibAdd
open DataResult
open ForeignData
open ForeignType
open TBrandContext
open TBrandModel

val mk_brand_relation :
  foreign_data -> (char list * char list) list -> brand_relation qresult

val mk_brand_context :
  foreign_type -> brand_relation -> brand_context_decls -> brand_context

val make_brand_model_from_decls_fails :
  foreign_data -> foreign_type -> brand_relation -> brand_context_decls ->
  brand_model qresult
