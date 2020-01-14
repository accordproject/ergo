open EquivDec
open List0
open Nat

type digit = int

val nat_to_digits_backwards : int -> int -> digit list

val nat_to_digits : int -> int -> digit list

val digit_to_char : int -> digit -> char

val list_to_string : char list -> char list

val digits_to_string_aux : int -> digit list -> char list

val digits_to_string : int -> digit list -> char list

val nat_to_string : int -> int -> char list

val nat_to_string10 : int -> char list

val coq_Z_to_string10 : int -> char list

val nat_to_string16 : int -> char list
