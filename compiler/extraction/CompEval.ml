open BrandRelation
open ForeignType
open TBrandModel

(** val h : foreign_type -> brand_model -> (char list * char list) list **)

let h _ bm =
  brand_relation_brands bm.brand_model_relation
