open Assoc
open Datatypes
open EquivDec
open List0

val compatible_with :
  'a1 coq_EqDec -> 'a2 coq_EqDec -> 'a1 -> 'a2 -> ('a1 * 'a2) list -> bool

val compatible :
  'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) list -> ('a1 * 'a2) list ->
  bool
