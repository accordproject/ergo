open BinaryOperators
open Data
open Datatypes
open ForeignRuntime
open NNRS
open NNRSCrossShadow
open NNRSimp
open UnaryOperators

val nnrs_expr_to_nnrs_imp_expr :
  foreign_runtime -> nnrs_expr -> nnrs_imp_expr

val nnrs_stmt_to_nnrs_imp_stmt : foreign_runtime -> nnrs_stmt -> nnrs_imp_stmt

val nnrs_to_nnrs_imp : foreign_runtime -> nnrs -> nnrs_imp

val nnrs_to_nnrs_imp_top : foreign_runtime -> char list -> nnrs -> nnrs_imp
