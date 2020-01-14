open Assoc
open Compat
open CoqLibAdd
open Datatypes
open EquivDec
open List0
open SortingAdd
open String0
open StringAdd

type 'k coq_ODT = { coq_ODT_eqdec : 'k coq_EqDec;
                    coq_ODT_lt_dec : ('k -> 'k -> bool);
                    coq_ODT_compare : ('k -> 'k -> comparison) }

val rec_field_lt_dec : 'a1 coq_ODT -> ('a1 * 'a2) -> ('a1 * 'a2) -> bool

val rec_sort : 'a1 coq_ODT -> ('a1 * 'a2) list -> ('a1 * 'a2) list

val rec_concat_sort :
  'a1 coq_ODT -> ('a1 * 'a2) list -> ('a1 * 'a2) list -> ('a1 * 'a2) list

val coq_ODT_string : char list coq_ODT

val edot : (char list * 'a1) list -> char list -> 'a1 option

val merge_bindings :
  'a1 coq_EqDec -> (char list * 'a1) list -> (char list * 'a1) list ->
  (char list * 'a1) list option

val rproject :
  (char list * 'a1) list -> char list list -> (char list * 'a1) list

val rremove : (char list * 'a1) list -> char list -> (char list * 'a1) list
