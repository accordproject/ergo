open Datatypes
open List0
open NativeString

val nstring_multi_append : nstring -> ('a1 -> nstring) -> 'a1 list -> nstring

val get_local_part : char list -> char list option

val find_duplicate : char list list -> char list option

val filter_some : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val postpend : 'a1 list -> 'a1 -> 'a1 list

val last_some_pair : ('a1 option * 'a2 option) list -> 'a1 option * 'a2 option

val coq_coq_distinct : ('a1 -> char list) -> 'a1 list -> 'a1 list

val coq_coq_toposort :
  ('a1 -> 'a2) -> ('a1 -> char list) -> ('a1 * 'a1 list) list -> 'a1 list

val coq_coq_sort_given_topo_order :
  'a1 list -> ('a1 -> char list) -> ('a2 -> char list) -> ('a1 -> char list)
  -> 'a2 list -> 'a2 list

val coq_coq_time : char list -> ('a1 -> 'a2) -> 'a1 -> 'a2
