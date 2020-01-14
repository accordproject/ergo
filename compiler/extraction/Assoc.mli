open Datatypes
open List0

val lookup : ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option

val update_first :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 -> ('a1 * 'a2) list

val domain : ('a1 * 'a2) list -> 'a1 list

val assoc_lookupr :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option

val lookup_diff :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> ('a1 * 'a3) list -> ('a1 * 'a2)
  list
