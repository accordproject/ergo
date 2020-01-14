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

(** val coq_ToString_nat_binary_op : nat_arith_binary_op coq_ToString **)

let coq_ToString_nat_binary_op = function
| NatPlus -> 'N'::('a'::('t'::('P'::('l'::('u'::('s'::[]))))))
| NatMinus -> 'N'::('a'::('t'::('M'::('i'::('n'::('u'::('s'::[])))))))
| NatMult -> 'N'::('a'::('t'::('M'::('u'::('l'::('t'::[]))))))
| NatDiv -> 'N'::('a'::('t'::('D'::('i'::('v'::[])))))
| NatRem -> 'N'::('a'::('t'::('R'::('e'::('m'::[])))))
| NatMin -> 'N'::('a'::('t'::('M'::('i'::('n'::[])))))
| NatMax -> 'N'::('a'::('t'::('M'::('a'::('x'::[])))))

(** val coq_ToString_float_arith_binary_op :
    float_arith_binary_op coq_ToString **)

let coq_ToString_float_arith_binary_op = function
| FloatPlus -> 'F'::('l'::('o'::('a'::('t'::('P'::('l'::('u'::('s'::[]))))))))
| FloatMinus ->
  'F'::('l'::('o'::('a'::('t'::('M'::('i'::('n'::('u'::('s'::[])))))))))
| FloatMult -> 'F'::('l'::('o'::('a'::('t'::('M'::('u'::('l'::('t'::[]))))))))
| FloatDiv -> 'F'::('l'::('o'::('a'::('t'::('D'::('i'::('v'::[])))))))
| FloatPow -> 'F'::('l'::('o'::('a'::('t'::('P'::('o'::('w'::[])))))))
| FloatMin -> 'F'::('l'::('o'::('a'::('t'::('M'::('i'::('n'::[])))))))
| FloatMax -> 'F'::('l'::('o'::('a'::('t'::('M'::('a'::('x'::[])))))))

(** val coq_ToString_float_compare_binary_op :
    float_compare_binary_op coq_ToString **)

let coq_ToString_float_compare_binary_op = function
| FloatLt -> 'F'::('l'::('o'::('a'::('t'::('L'::('t'::[]))))))
| FloatLe -> 'F'::('l'::('o'::('a'::('t'::('L'::('e'::[]))))))
| FloatGt -> 'F'::('l'::('o'::('a'::('t'::('G'::('t'::[]))))))
| FloatGe -> 'F'::('l'::('o'::('a'::('t'::('G'::('e'::[]))))))

(** val coq_ToString_binary_op :
    foreign_data -> foreign_operators -> binary_op coq_ToString **)

let coq_ToString_binary_op _ foperators = function
| OpEqual -> 'O'::('p'::('E'::('q'::('u'::('a'::('l'::[]))))))
| OpRecConcat ->
  'O'::('p'::('R'::('e'::('c'::('C'::('o'::('n'::('c'::('a'::('t'::[]))))))))))
| OpRecMerge ->
  'O'::('p'::('R'::('e'::('c'::('M'::('e'::('r'::('g'::('e'::[])))))))))
| OpAnd -> 'O'::('p'::('A'::('n'::('d'::[]))))
| OpOr -> 'O'::('p'::('O'::('r'::[])))
| OpLt -> 'O'::('p'::('L'::('t'::[])))
| OpLe -> 'O'::('p'::('L'::('e'::[])))
| OpBagUnion ->
  'O'::('p'::('B'::('a'::('g'::('U'::('n'::('i'::('o'::('n'::[])))))))))
| OpBagDiff -> 'O'::('p'::('B'::('a'::('g'::('D'::('i'::('f'::('f'::[]))))))))
| OpBagMin -> 'O'::('p'::('B'::('a'::('g'::('M'::('i'::('n'::[])))))))
| OpBagMax -> 'O'::('p'::('B'::('a'::('g'::('M'::('a'::('x'::[])))))))
| OpBagNth -> 'O'::('p'::('B'::('a'::('g'::('N'::('t'::('h'::[])))))))
| OpContains ->
  'O'::('p'::('C'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::[])))))))))
| OpStringConcat ->
  'O'::('p'::('S'::('t'::('r'::('i'::('n'::('g'::('C'::('o'::('n'::('c'::('a'::('t'::[])))))))))))))
| OpStringJoin ->
  'O'::('p'::('S'::('t'::('r'::('i'::('n'::('g'::('J'::('o'::('i'::('n'::[])))))))))))
| OpNatBinary aop ->
  append
    ('('::('O'::('p'::('N'::('a'::('t'::('B'::('i'::('n'::('a'::('r'::('y'::(' '::[])))))))))))))
    (append (toString coq_ToString_nat_binary_op aop) (')'::[]))
| OpFloatBinary aop ->
  append
    ('('::('O'::('p'::('F'::('l'::('o'::('a'::('t'::('B'::('i'::('n'::('a'::('r'::('y'::(' '::[])))))))))))))))
    (append (toString coq_ToString_float_arith_binary_op aop) (')'::[]))
| OpFloatCompare aop ->
  append
    ('('::('O'::('p'::('F'::('l'::('o'::('a'::('t'::('C'::('o'::('m'::('p'::('a'::('r'::('e'::(' '::[]))))))))))))))))
    (append (toString coq_ToString_float_compare_binary_op aop) (')'::[]))
| OpForeignBinary fb ->
  toString foperators.foreign_operators_binary_tostring fb
