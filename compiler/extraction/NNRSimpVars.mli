open CoqLibAdd
open Datatypes
open ForeignRuntime
open List0
open NNRSimp
open Var

val nnrs_imp_expr_free_vars : foreign_runtime -> nnrs_imp_expr -> var list

val nnrs_imp_stmt_free_vars : foreign_runtime -> nnrs_imp_stmt -> var list

val nnrs_imp_stmt_bound_vars : foreign_runtime -> nnrs_imp_stmt -> var list
