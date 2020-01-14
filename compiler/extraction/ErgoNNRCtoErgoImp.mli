open Datatypes
open ErgoImp
open ErgoNNRC
open List0
open QLib
open TBrandModel

val ergo_nnrc_function_to_imp :
  brand_model -> char list list -> ergo_nnrc_lambda -> ergo_imp_lambda

val ergo_nnrc_function_table_to_imp :
  brand_model -> char list list -> ergo_nnrc_function_table ->
  ergo_imp_function_table

val ergo_nnrc_declaration_to_imp :
  brand_model -> char list list -> ergo_nnrc_declaration ->
  ergo_imp_declaration

val ergo_nnrc_declarations_to_imp :
  brand_model -> ergo_nnrc_declaration list -> ergo_imp_declaration list

val ergo_nnrc_module_to_imp :
  brand_model -> ergo_nnrc_module -> ergo_imp_module
