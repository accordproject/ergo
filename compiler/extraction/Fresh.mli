open CoqLibAdd
open Datatypes
open Digits
open EquivDec
open List0
open Nat
open String0
open StringAdd

val find_bounded : ('a1 -> 'a1) -> ('a1 -> bool) -> int -> 'a1 -> 'a1 option

val find_bounded_S_nin_finds :
  (int -> 'a1) -> 'a1 coq_EqDec -> 'a1 list -> int -> 'a1

val find_fresh_inj_f : 'a1 coq_EqDec -> (int -> 'a1) -> 'a1 list -> 'a1

val find_fresh_string : char list list -> char list

val fresh_var : char list -> char list list -> char list

val fresh_var2 :
  char list -> char list -> char list list -> char list * char list

val get_var_base : char list -> char list -> char list

val fresh_var_from : char list -> char list -> char list list -> char list
