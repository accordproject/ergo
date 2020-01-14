open CoqLibAdd
open Datatypes
open EquivDec
open List0
open ListSet
open SortingAdd
open String0
open StringAdd

type brand = char list

type brands = brand list

type brand_relation_t = (char list * char list) list

val brand_relation_trans_dec : brand_relation_t -> bool

val brand_relation_assym_dec : brand_relation_t -> bool

type brand_relation =
  (char list * char list) list
  (* singleton inductive, whose constructor was mkBrand_relation *)

val brand_relation_brands : brand_relation -> (char list * char list) list

val sub_brand_dec : brand_relation_t -> brand -> brand -> bool

val sub_brands_dec : brand_relation_t -> brands -> brands -> bool

val parents : brand_relation_t -> brand -> char list list

val parents_and_self : brand_relation_t -> brand -> brand list

val explode_brands : brand_relation_t -> brands -> brand list

val has_subtype_in : brand_relation_t -> brands -> brand -> bool

val collapse_brands : brand_relation_t -> brands -> brand list

val canon_brands : brand_relation_t -> brands -> char list list

val is_canon_brands_dec : brand_relation_t -> brands -> bool

val brand_join : brand_relation_t -> brands -> brands -> char list list

val brand_meet : brand_relation_t -> brands -> brands -> char list list

val coq_ToString_brands : brands coq_ToString
