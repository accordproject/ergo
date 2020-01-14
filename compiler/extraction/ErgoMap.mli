open Ast
open Datatypes
open Ergo
open List0
open Misc
open Result0

val ergo_map_expr :
  ('a4 -> char list -> ('a1, 'a2, 'a3) ergo_expr -> 'a4) -> ('a4 -> ('a1,
  'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult option) -> 'a4 ->
  ('a1, 'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult
