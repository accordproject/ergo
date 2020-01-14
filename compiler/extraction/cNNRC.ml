open BinaryOperators
open Data
open UnaryOperators
open Var

type nnrc =
| NNRCGetConstant of var
| NNRCVar of var
| NNRCConst of data
| NNRCBinop of binary_op * nnrc * nnrc
| NNRCUnop of unary_op * nnrc
| NNRCLet of var * nnrc * nnrc
| NNRCFor of var * nnrc * nnrc
| NNRCIf of nnrc * nnrc * nnrc
| NNRCEither of nnrc * var * nnrc * var * nnrc
| NNRCGroupBy of char list * char list list * nnrc
