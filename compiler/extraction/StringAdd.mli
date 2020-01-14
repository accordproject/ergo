open Ascii
open CoqLibAdd
open Datatypes
open EquivDec
open List0
open Nat
open String0

module AsciiOrder :
 sig
  val compare : char -> char -> comparison
 end

module StringOrder :
 sig
  val compare : char list -> char list -> comparison

  val lt_dec : char list -> char list -> bool
 end

val map_string : (char -> char) -> char list -> char list

val ascii_dec : char coq_EqDec

val map_concat : char list -> ('a1 -> char list) -> 'a1 list -> char list

val string_reverse_helper : char list -> char list -> char list

val string_reverse : char list -> char list

type like_clause =
| Coq_like_literal of char list
| Coq_like_any_char
| Coq_like_any_string

val make_like_clause : char list -> char option -> like_clause list

val string_exists_suffix : (char list -> bool) -> char list -> bool

val like_clause_matches_string : like_clause list -> char list -> bool

val string_like : char list -> char list -> char option -> bool
