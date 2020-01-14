open Assoc
open BrandRelation
open Datatypes
open ForeignType
open List0
open ListAdd
open RSubtype
open String0
open TBrandContext

(** val brand_model_domain_dec :
    foreign_type -> brand_relation -> brand_context -> bool **)

let brand_model_domain_dec ftype br m =
  incl_list_dec string_dec (domain (brand_relation_brands br))
    (domain (brand_context_types ftype br m))

(** val brand_model_subtype_weak_dec :
    foreign_type -> brand_relation -> brand_context -> bool **)

let brand_model_subtype_weak_dec ftype br m =
  if forallb (fun ab ->
       match lookup string_dec (brand_context_types ftype br m) (fst ab) with
       | Some ta ->
         (match lookup string_dec (brand_context_types ftype br m) (snd ab) with
          | Some tb -> if subtype_dec ftype br ta tb then true else false
          | None -> false)
       | None -> true) (brand_relation_brands br)
  then true
  else false

type brand_model = { brand_model_relation : brand_relation;
                     brand_model_context : brand_context }

(** val make_brand_model :
    foreign_type -> brand_relation -> brand_context -> brand_model **)

let make_brand_model ftype b m =
  if brand_model_domain_dec ftype b m
  then if brand_model_subtype_weak_dec ftype b m
       then { brand_model_relation = b; brand_model_context = m }
       else assert false (* absurd case *)
  else assert false (* absurd case *)

(** val empty_brand_model : foreign_type -> brand_model **)

let empty_brand_model ftype =
  make_brand_model ftype [] []
