open BinInt
open Datatypes
open EquivDec
open List0

val bunion : 'a1 list -> 'a1 list -> 'a1 list

val remove_one : 'a1 coq_EqDec -> 'a1 -> 'a1 list -> 'a1 list

val bminus : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list

val mult : 'a1 coq_EqDec -> 'a1 list -> 'a1 -> int

val bmin : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list

val bmax : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list

val bcount : 'a1 list -> int

val bdistinct : 'a1 coq_EqDec -> 'a1 list -> 'a1 list

val bnummin : int list -> int

val bnummax : int list -> int
