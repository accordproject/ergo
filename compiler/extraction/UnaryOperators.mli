open BrandRelation
open CoqLibAdd
open EmitUtil
open ForeignData
open ForeignOperators
open List0
open SortingDesc
open String0
open ToString

type nat_arith_unary_op =
| NatAbs
| NatLog2
| NatSqrt

type float_arith_unary_op =
| FloatNeg
| FloatSqrt
| FloatExp
| FloatLog
| FloatLog10
| FloatCeil
| FloatFloor
| FloatAbs

type unary_op =
| OpIdentity
| OpNeg
| OpRec of char list
| OpDot of char list
| OpRecRemove of char list
| OpRecProject of char list list
| OpBag
| OpSingleton
| OpFlatten
| OpDistinct
| OpOrderBy of coq_SortCriterias
| OpCount
| OpToString
| OpToText
| OpLength
| OpSubstring of int * int option
| OpLike of char list
| OpLeft
| OpRight
| OpBrand of brands
| OpUnbrand
| OpCast of brands
| OpNatUnary of nat_arith_unary_op
| OpNatSum
| OpNatMin
| OpNatMax
| OpNatMean
| OpFloatOfNat
| OpFloatUnary of float_arith_unary_op
| OpFloatTruncate
| OpFloatSum
| OpFloatMean
| OpFloatBagMin
| OpFloatBagMax
| OpForeignUnary of foreign_operators_unary

val coq_ToString_nat_arith_unary_op : nat_arith_unary_op coq_ToString

val coq_ToString_float_arith_unary_op : float_arith_unary_op coq_ToString

val coq_ToString_SortDesc : coq_SortDesc -> char list

val coq_ToString_SortCriteria : (char list * coq_SortDesc) -> char list

val coq_ToString_unary_op :
  foreign_data -> foreign_operators -> unary_op coq_ToString
