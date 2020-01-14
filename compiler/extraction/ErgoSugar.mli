open Ast
open Data
open Ergo
open Names

val coq_SReturnEmpty : 'a1 -> ('a1, 'a2) rergo_stmt

val coq_EFunReturnEmpty : 'a1 -> ('a1, 'a2) rergo_expr

val coq_EOptionalDot :
  'a1 -> char list -> ('a1, 'a2) rergo_expr -> ('a1, 'a2, relative_name)
  ergo_expr

val coq_EOptionalDefault :
  'a1 -> ('a1, 'a2) rergo_expr -> ('a1, 'a2) rergo_expr -> ('a1, 'a2,
  relative_name) ergo_expr
