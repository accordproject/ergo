open BinaryOperators
open Datatypes
open EquivDec
open ForeignData
open ForeignDataTyping
open ForeignOperators
open ForeignOperatorsTyping
open ForeignType
open Lattice
open Lift
open List0
open RSubtype
open RType
open RTypeLattice
open TBrandModel
open TBrandModelProp
open TOperatorsInfer
open TUtil
open UnaryOperators

val infer_binary_op_type_sub :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
  foreign_operators -> foreign_operators_typing -> binary_op -> rtype ->
  rtype -> ((rtype * rtype) * rtype) option

val infer_unary_op_type_sub :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
  foreign_operators -> foreign_operators_typing -> unary_op -> rtype ->
  (rtype * rtype) option
