open BinaryOperators
open Data
open UnaryOperators
open Var

type nnrs_imp_expr =
| NNRSimpGetConstant of var
| NNRSimpVar of var
| NNRSimpConst of data
| NNRSimpBinop of binary_op * nnrs_imp_expr * nnrs_imp_expr
| NNRSimpUnop of unary_op * nnrs_imp_expr
| NNRSimpGroupBy of char list * char list list * nnrs_imp_expr

type nnrs_imp_stmt =
| NNRSimpSkip
| NNRSimpSeq of nnrs_imp_stmt * nnrs_imp_stmt
| NNRSimpAssign of var * nnrs_imp_expr
| NNRSimpLet of var * nnrs_imp_expr option * nnrs_imp_stmt
| NNRSimpFor of var * nnrs_imp_expr * nnrs_imp_stmt
| NNRSimpIf of nnrs_imp_expr * nnrs_imp_stmt * nnrs_imp_stmt
| NNRSimpEither of nnrs_imp_expr * var * nnrs_imp_stmt * var * nnrs_imp_stmt

type nnrs_imp = nnrs_imp_stmt * var
