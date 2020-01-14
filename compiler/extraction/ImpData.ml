open BinaryOperators
open Data
open Imp
open UnaryOperators

type imp_data_constant = data

type imp_data_op =
| DataOpUnary of unary_op
| DataOpBinary of binary_op

type imp_data_runtime_op =
| DataRuntimeGroupby of char list * char list list
| DataRuntimeEither
| DataRuntimeToLeft
| DataRuntimeToRight

type imp_data_expr =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_expr

type imp_data_stmt =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_stmt

type imp_data_function =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_function

type imp_data = (imp_data_constant, imp_data_op, imp_data_runtime_op) imp
