open Ast
open BinaryOperators
open Data
open Datatypes
open Ergo
open ErgoCT
open ErgoNNRC
open ErgoNNRCSugar
open ForeignRuntime
open Fresh
open List0
open Names
open QcertData
open Result0
open String0
open TBrandModel
open UnaryOperators
open CNNRC

val ergo_pattern_to_nnrc :
  brand_model -> char list list -> ergo_nnrc_expr -> tlaergo_pattern ->
  char list list * ergo_nnrc_expr

val pack_pattern :
  char list list -> ergo_nnrc_expr -> ergo_nnrc_expr -> ergo_nnrc_expr ->
  ergo_nnrc_expr

val ergoct_expr_to_nnrc :
  brand_model -> char list list -> ergoct_expr -> ergo_nnrc_expr eresult

val functionct_to_nnrc :
  brand_model -> absolute_name -> ergoct_function ->
  (char list * ergo_nnrc_lambda) eresult

val clausect_declaration_to_nnrc :
  brand_model -> absolute_name -> ergoct_function ->
  (char list * ergo_nnrc_lambda) eresult

val contractct_to_nnrc :
  brand_model -> ergoct_contract -> ergo_nnrc_function_table eresult

val declarationct_to_nnrc :
  brand_model -> ergoct_declaration -> ergo_nnrc_declaration list eresult

val declarationsct_calculus_with_table :
  brand_model -> ergoct_declaration list -> ergo_nnrc_declaration list eresult

val modulect_to_nnrc_with_table :
  brand_model -> ergoct_module -> ergo_nnrc_module eresult

val ergoct_module_to_nnrc :
  brand_model -> ergoct_module -> ergo_nnrc_module eresult
