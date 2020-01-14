open Bag
open BinInt
open BinaryOperators
open Bindings
open BrandRelation
open CoqLibAdd
open Data
open DataLift
open Datatypes
open ForeignData
open ForeignOperators
open List0
open OperatorsUtils
open String0
open ZArith_dec

val nat_arith_binary_op_eval : nat_arith_binary_op -> int -> int -> int

val float_arith_binary_op_eval :
  float_arith_binary_op -> float -> float -> float

val float_compare_binary_op_eval :
  float_compare_binary_op -> float -> float -> bool

val binary_op_eval :
  brand_relation_t -> foreign_data -> foreign_operators -> binary_op -> data
  -> data -> data option
