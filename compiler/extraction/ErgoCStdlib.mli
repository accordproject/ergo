open BinaryOperators
open Datatypes
open DateTimeComponent
open Ergo
open ErgoC
open ErgoType
open List0
open MathComponent
open MonetaryAmountComponent
open Names
open Provenance
open QcertData
open UnaryOperators
open UriComponent

val empty_sigc : char list list -> provenance -> sigc

val mk_naked_closure :
  char list list -> ergoc_expr -> provenance -> ergoc_function

val mk_unary : QLib.QcertOps.Unary.op -> provenance -> ergoc_function

val mk_binary_expr : ergoc_expr -> provenance -> ergoc_function

val mk_binary : QLib.QcertOps.Binary.op -> provenance -> ergoc_function

type ergo_stdlib_table = (char list * (provenance -> ergoc_function)) list

val backend_compose_table :
  ergo_stdlib_table -> ergo_stdlib_table -> ergo_stdlib_table

val foreign_unary_operator_table : ergo_stdlib_table

val foreign_binary_operator_table : ergo_stdlib_table

val foreign_table : ergo_stdlib_table

val unary_operator_table : ergo_stdlib_table

val binary_operator_table : ergo_stdlib_table

val builtin_table : ergo_stdlib_table

val ergoc_stdlib : ergo_stdlib_table
