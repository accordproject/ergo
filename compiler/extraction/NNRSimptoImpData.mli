open Datatypes
open ForeignRuntime
open Fresh
open Imp
open ImpData
open Lift
open NNRSimp
open NNRSimpVars
open UnaryOperators

val nnrs_imp_expr_to_imp_data :
  foreign_runtime -> char list -> nnrs_imp_expr -> imp_data_expr

val nnrs_imp_stmt_to_imp_data :
  foreign_runtime -> char list -> nnrs_imp_stmt -> imp_data_stmt

val nnrs_imp_to_imp_data_function :
  foreign_runtime -> nnrs_imp -> (imp_data_constant, imp_data_op,
  imp_data_runtime_op) imp_function

val nnrs_imp_to_imp_data_top :
  foreign_runtime -> char list -> nnrs_imp -> (imp_data_constant,
  imp_data_op, imp_data_runtime_op) imp
