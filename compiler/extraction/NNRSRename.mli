open CoqLibAdd
open EquivDec
open ForeignRuntime
open NNRS
open Var

val nnrs_stmt_rename_mc :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt

val nnrs_stmt_rename_md :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt

val nnrs_expr_rename_env :
  foreign_runtime -> nnrs_expr -> var -> var -> nnrs_expr

val nnrs_stmt_rename_env :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt
