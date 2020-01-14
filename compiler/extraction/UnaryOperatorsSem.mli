open Bag
open BinInt
open BinPos
open Bindings
open BrandRelation
open CoqLibAdd
open Data
open DataLift
open Datatypes
open ForeignData
open ForeignOperators
open Iterators
open Lift
open Nat
open OperatorsUtils
open SortBy
open String0
open StringAdd
open UnaryOperators

val nat_arith_unary_op_eval : nat_arith_unary_op -> int -> int

val float_arith_unary_op_eval : float_arith_unary_op -> float -> float

val coq_ToString_data : foreign_data -> foreign_operators -> data coq_ToString

val unary_op_eval :
  foreign_data -> brand_relation_t -> foreign_operators -> unary_op -> data
  -> data option
