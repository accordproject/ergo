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

(** val brand_relation_trans_dec : brand_relation_t -> bool **)

let brand_relation_trans_dec brand_relation_brands0 =
  if forallb (fun ab ->
       forallb (fun bc ->
         if string_dec (snd ab) (fst bc)
         then set_mem (pair_eqdec string_eqdec string_eqdec) ((fst ab),
                (snd bc)) brand_relation_brands0
         else true) brand_relation_brands0) brand_relation_brands0
  then true
  else false

(** val brand_relation_assym_dec : brand_relation_t -> bool **)

let brand_relation_assym_dec brand_relation_brands0 =
  if forallb (fun ab ->
       negb
         (set_mem (pair_eqdec string_eqdec string_eqdec) ((snd ab), (fst ab))
           brand_relation_brands0)) brand_relation_brands0
  then true
  else false

type brand_relation =
  (char list * char list) list
  (* singleton inductive, whose constructor was mkBrand_relation *)

(** val brand_relation_brands :
    brand_relation -> (char list * char list) list **)

let brand_relation_brands brand_relation0 =
  brand_relation0

(** val sub_brand_dec : brand_relation_t -> brand -> brand -> bool **)

let sub_brand_dec br a b =
  let s = equiv_dec string_eqdec a b in
  if s
  then true
  else in_dec (equiv_dec (pair_eqdec string_eqdec string_eqdec)) (a, b) br

(** val sub_brands_dec : brand_relation_t -> brands -> brands -> bool **)

let sub_brands_dec br a b =
  forall_in_dec b (fun x _ ->
    exists_in_dec a (fun x0 _ -> sub_brand_dec br x0 x))

(** val parents : brand_relation_t -> brand -> char list list **)

let parents hs a =
  map snd
    (filter (fun x ->
      if equiv_dec string_eqdec a (fst x) then true else false) hs)

(** val parents_and_self : brand_relation_t -> brand -> brand list **)

let parents_and_self hs a =
  a :: (parents hs a)

(** val explode_brands : brand_relation_t -> brands -> brand list **)

let explode_brands hs a =
  flat_map (parents_and_self hs) a

(** val has_subtype_in : brand_relation_t -> brands -> brand -> bool **)

let has_subtype_in hs c a =
  existsb (fun x ->
    if in_dec (equiv_dec (pair_eqdec string_eqdec string_eqdec)) (x, a) hs
    then true
    else false) c

(** val collapse_brands : brand_relation_t -> brands -> brand list **)

let collapse_brands hs c =
  filter (fun x -> negb (has_subtype_in hs c x)) c

(** val canon_brands : brand_relation_t -> brands -> char list list **)

let canon_brands hs a =
  insertion_sort StringOrder.lt_dec (collapse_brands hs a)

(** val is_canon_brands_dec : brand_relation_t -> brands -> bool **)

let is_canon_brands_dec hs a =
  list_eqdec string_dec (canon_brands hs a) a

(** val brand_join :
    brand_relation_t -> brands -> brands -> char list list **)

let brand_join hs a b =
  canon_brands hs
    (set_inter string_dec (explode_brands hs a) (explode_brands hs b))

(** val brand_meet :
    brand_relation_t -> brands -> brands -> char list list **)

let brand_meet hs a b =
  canon_brands hs (app a b)

(** val coq_ToString_brands : brands coq_ToString **)

let coq_ToString_brands b =
  concat (' '::('&'::(' '::[]))) b
