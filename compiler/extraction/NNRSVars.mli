open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open List0
open NNRS
open Var

val nnrs_expr_free_vars : foreign_runtime -> nnrs_expr -> var list

val nnrs_stmt_free_env_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_free_mcenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_free_mdenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_env_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_mcenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_mdenv_vars : foreign_runtime -> nnrs_stmt -> var list
