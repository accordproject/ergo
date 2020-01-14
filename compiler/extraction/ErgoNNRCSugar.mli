open BinaryOperators
open Data
open Datatypes
open ErgoNNRC
open Fresh
open List0
open QcertData
open UnaryOperators
open CNNRC
open CNNRCVars

val fresh_in_match :
  ('a1 * ergo_nnrc_expr) list -> ergo_nnrc_expr -> char list

val fresh_in_case : ergo_nnrc_expr -> ergo_nnrc_expr -> char list

val new_array : ergo_nnrc_expr list -> ergo_nnrc_expr

val new_expr : char list -> ergo_nnrc_expr -> ergo_nnrc_expr
