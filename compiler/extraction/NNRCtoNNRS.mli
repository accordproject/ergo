open Datatypes
open ForeignRuntime
open Fresh
open Lift
open NNRC
open NNRCStratify
open NNRS
open Var
open CNNRC
open CNNRCVars

val nnrc_expr_to_nnrs_expr : foreign_runtime -> NNRC.nnrc -> nnrs_expr option

val nnrc_expr_to_nnrs_expr_stratified_some :
  foreign_runtime -> NNRC.nnrc -> nnrs_expr

type terminator =
| Term_assign of var
| Term_push of var

val terminate : foreign_runtime -> terminator -> nnrs_expr -> nnrs_stmt

val nnrc_stmt_to_nnrs_stmt_aux :
  foreign_runtime -> var list -> terminator -> NNRC.nnrc -> nnrs_stmt option

val nnrc_stmt_to_nnrs :
  foreign_runtime -> var list -> NNRC.nnrc -> (nnrs_stmt * var) option

val nnrc_stmt_to_nnrs_stmt_aux_stratified_some :
  foreign_runtime -> var list -> terminator -> NNRC.nnrc -> nnrs_stmt

val nnrc_stmt_to_nnrs_stmt_stratified_some :
  foreign_runtime -> var list -> NNRC.nnrc -> (nnrs_stmt * var)

val stratified_nnrc_stmt_to_nnrs :
  foreign_runtime -> var list -> NNRC.nnrc -> nnrs

val nnrc_to_nnrs_top : foreign_runtime -> var list -> NNRC.nnrc -> nnrs
