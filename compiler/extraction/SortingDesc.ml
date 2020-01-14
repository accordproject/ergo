open BinInt
open Datatypes
open List0
open SortingAdd
open StringAdd

type coq_SortDesc =
| Descending
| Ascending

type coq_SortCriteria = char list * coq_SortDesc

type coq_SortCriterias = coq_SortCriteria list

type sdata =
| Coq_sdnat of int
| Coq_sdstring of char list

module SortableDataOrder =
 struct
  type t = sdata

  (** val compare : t -> t -> comparison **)

  let compare d1 d2 =
    match d1 with
    | Coq_sdnat n1 ->
      (match d2 with
       | Coq_sdnat n2 -> Z.compare n1 n2
       | Coq_sdstring _ -> Lt)
    | Coq_sdstring s1 ->
      (match d2 with
       | Coq_sdnat _ -> Gt
       | Coq_sdstring s2 -> StringOrder.compare s1 s2)
 end

module LexicographicDataOrder =
 struct
  type t = sdata list

  (** val compare : sdata list -> sdata list -> comparison **)

  let rec compare l1 l2 =
    match l1 with
    | [] -> (match l2 with
             | [] -> Eq
             | _ :: _ -> Lt)
    | d1 :: l1' ->
      (match l2 with
       | [] -> Gt
       | d2 :: l2' ->
         (match SortableDataOrder.compare d1 d2 with
          | Eq -> compare l1' l2'
          | x -> x))

  (** val le_dec : t -> t -> bool **)

  let le_dec a b =
    let filtered_var = compare a b in
    (match filtered_var with
     | Gt -> false
     | _ -> true)
 end

type 'a sortable_data = sdata list * 'a

type 'a sortable_coll = 'a sortable_data list

(** val dict_field_le_dec : 'a1 sortable_data -> 'a1 sortable_data -> bool **)

let dict_field_le_dec a b =
  let (l, _) = a in let (l0, _) = b in LexicographicDataOrder.le_dec l l0

(** val dict_sort : (sdata list * 'a1) list -> (sdata list * 'a1) list **)

let dict_sort l =
  insertion_sort dict_field_le_dec l

(** val sort_sortable_coll : 'a1 sortable_coll -> 'a1 sortable_coll **)

let sort_sortable_coll =
  dict_sort

(** val coll_of_sortable_coll : 'a1 sortable_coll -> 'a1 list **)

let coll_of_sortable_coll sc =
  map snd sc
