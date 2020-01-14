open BinaryOperators
open Data
open UnaryOperators
open Var

type nnrs_expr =
| NNRSGetConstant of var
| NNRSVar of var
| NNRSConst of data
| NNRSBinop of binary_op * nnrs_expr * nnrs_expr
| NNRSUnop of unary_op * nnrs_expr
| NNRSGroupBy of char list * char list list * nnrs_expr

type nnrs_stmt =
| NNRSSeq of nnrs_stmt * nnrs_stmt
| NNRSLet of var * nnrs_expr * nnrs_stmt
| NNRSLetMut of var * nnrs_stmt * nnrs_stmt
| NNRSLetMutColl of var * nnrs_stmt * nnrs_stmt
| NNRSAssign of var * nnrs_expr
| NNRSPush of var * nnrs_expr
| NNRSFor of var * nnrs_expr * nnrs_stmt
| NNRSIf of nnrs_expr * nnrs_stmt * nnrs_stmt
| NNRSEither of nnrs_expr * var * nnrs_stmt * var * nnrs_stmt

type nnrs = nnrs_stmt * var
