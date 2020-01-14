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

module SortableDataOrder :
 sig
  type t = sdata

  val compare : t -> t -> comparison
 end

module LexicographicDataOrder :
 sig
  type t = sdata list

  val compare : sdata list -> sdata list -> comparison

  val le_dec : t -> t -> bool
 end

type 'a sortable_data = sdata list * 'a

type 'a sortable_coll = 'a sortable_data list

val dict_field_le_dec : 'a1 sortable_data -> 'a1 sortable_data -> bool

val dict_sort : (sdata list * 'a1) list -> (sdata list * 'a1) list

val sort_sortable_coll : 'a1 sortable_coll -> 'a1 sortable_coll

val coll_of_sortable_coll : 'a1 sortable_coll -> 'a1 list
