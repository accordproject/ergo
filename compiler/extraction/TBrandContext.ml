open BrandRelation
open ForeignType
open RType

type brand_context_decls = (char list * rtype) list

type brand_context =
  brand_context_decls
  (* singleton inductive, whose constructor was mkBrand_context *)

(** val brand_context_types :
    foreign_type -> brand_relation -> brand_context -> brand_context_decls **)

let brand_context_types _ _ brand_context0 =
  brand_context0
