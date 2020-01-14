open CoqLibAdd
open ForeignData
open ForeignOperators
open String0

type nat_arith_binary_op =
| NatPlus
| NatMinus
| NatMult
| NatDiv
| NatRem
| NatMin
| NatMax

type float_arith_binary_op =
| FloatPlus
| FloatMinus
| FloatMult
| FloatDiv
| FloatPow
| FloatMin
| FloatMax

type float_compare_binary_op =
| FloatLt
| FloatLe
| FloatGt
| FloatGe

type binary_op =
| OpEqual
| OpRecConcat
| OpRecMerge
| OpAnd
| OpOr
| OpLt
| OpLe
| OpBagUnion
| OpBagDiff
| OpBagMin
| OpBagMax
| OpBagNth
| OpContains
| OpStringConcat
| OpStringJoin
| OpNatBinary of nat_arith_binary_op
| OpFloatBinary of float_arith_binary_op
| OpFloatCompare of float_compare_binary_op
| OpForeignBinary of foreign_operators_binary

val coq_ToString_nat_binary_op : nat_arith_binary_op coq_ToString

val coq_ToString_float_arith_binary_op : float_arith_binary_op coq_ToString

val coq_ToString_float_compare_binary_op :
  float_compare_binary_op coq_ToString

val coq_ToString_binary_op :
  foreign_data -> foreign_operators -> binary_op coq_ToString
