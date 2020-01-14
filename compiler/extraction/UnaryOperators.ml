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

(** val coq_ToString_nat_arith_unary_op : nat_arith_unary_op coq_ToString **)

let coq_ToString_nat_arith_unary_op = function
| NatAbs -> 'N'::('a'::('t'::('A'::('b'::('s'::[])))))
| NatLog2 -> 'N'::('a'::('t'::('L'::('o'::('g'::('2'::[]))))))
| NatSqrt -> 'N'::('a'::('t'::('S'::('q'::('r'::('t'::[]))))))

(** val coq_ToString_float_arith_unary_op :
    float_arith_unary_op coq_ToString **)

let coq_ToString_float_arith_unary_op = function
| FloatNeg -> 'F'::('l'::('o'::('a'::('t'::('N'::('e'::('g'::[])))))))
| FloatSqrt -> 'F'::('l'::('o'::('a'::('t'::('S'::('q'::('r'::('t'::[]))))))))
| FloatExp -> 'F'::('l'::('o'::('a'::('t'::('E'::('x'::('p'::[])))))))
| FloatLog -> 'F'::('l'::('o'::('a'::('t'::('L'::('o'::('g'::[])))))))
| FloatLog10 ->
  'F'::('l'::('o'::('a'::('t'::('L'::('o'::('g'::('1'::('0'::[])))))))))
| FloatCeil -> 'F'::('l'::('o'::('a'::('t'::('C'::('e'::('i'::('l'::[]))))))))
| FloatFloor ->
  'F'::('l'::('o'::('a'::('t'::('F'::('l'::('o'::('o'::('r'::[])))))))))
| FloatAbs -> 'F'::('l'::('o'::('a'::('t'::('A'::('b'::('s'::[])))))))

(** val coq_ToString_SortDesc : coq_SortDesc -> char list **)

let coq_ToString_SortDesc = function
| Descending -> 'd'::('e'::('s'::('c'::[])))
| Ascending -> 'a'::('s'::('c'::[]))

(** val coq_ToString_SortCriteria :
    (char list * coq_SortDesc) -> char list **)

let coq_ToString_SortCriteria = function
| (att, sd) ->
  string_bracket ('('::[])
    (append att (append (','::[]) (coq_ToString_SortDesc sd))) (')'::[])

(** val coq_ToString_unary_op :
    foreign_data -> foreign_operators -> unary_op coq_ToString **)

let coq_ToString_unary_op _ foperators = function
| OpIdentity ->
  'O'::('p'::('I'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::[])))))))))
| OpNeg -> 'O'::('p'::('N'::('e'::('g'::[]))))
| OpRec f ->
  append ('('::('O'::('p'::('R'::('e'::('c'::(' '::[])))))))
    (append f (')'::[]))
| OpDot s ->
  append ('('::('O'::('p'::('D'::('o'::('t'::(' '::[])))))))
    (append s (')'::[]))
| OpRecRemove s ->
  append
    ('('::('O'::('p'::('R'::('e'::('c'::('R'::('e'::('m'::('o'::('v'::('e'::(' '::[])))))))))))))
    (append s (')'::[]))
| OpRecProject ls ->
  append
    ('('::('O'::('p'::('R'::('e'::('c'::('P'::('r'::('o'::('j'::('e'::('c'::('t'::(' '::[]))))))))))))))
    (append (string_bracket ('['::[]) (concat (','::[]) ls) (']'::[]))
      (')'::[]))
| OpBag -> 'O'::('p'::('B'::('a'::('g'::[]))))
| OpSingleton ->
  'O'::('p'::('S'::('i'::('n'::('g'::('l'::('e'::('t'::('o'::('n'::[]))))))))))
| OpFlatten -> 'O'::('p'::('F'::('l'::('a'::('t'::('t'::('e'::('n'::[]))))))))
| OpDistinct ->
  'O'::('p'::('D'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::[])))))))))
| OpOrderBy ls ->
  append
    ('('::('O'::('p'::('O'::('r'::('d'::('e'::('r'::('B'::('y'::[]))))))))))
    (append
      (string_bracket ('['::[])
        (concat (','::[]) (map coq_ToString_SortCriteria ls)) (']'::[]))
      (')'::[]))
| OpCount -> 'O'::('p'::('C'::('o'::('u'::('n'::('t'::[]))))))
| OpToString ->
  'O'::('p'::('T'::('o'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))
| OpToText -> 'O'::('p'::('T'::('o'::('T'::('e'::('x'::('t'::[])))))))
| OpLength -> 'O'::('p'::('L'::('e'::('n'::('g'::('t'::('h'::[])))))))
| OpSubstring (start, len) ->
  append
    ('('::('O'::('p'::('S'::('u'::('b'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::[])))))))))))))
    (append (toString coq_ToString_Z start)
      (append
        (match len with
         | Some len0 -> append (' '::[]) (toString coq_ToString_Z len0)
         | None -> []) (')'::[])))
| OpLike pattern ->
  append ('('::('O'::('p'::('L'::('i'::('k'::('e'::(' '::[]))))))))
    (append pattern (')'::[]))
| OpLeft -> 'O'::('p'::('L'::('e'::('f'::('t'::[])))))
| OpRight -> 'O'::('p'::('R'::('i'::('g'::('h'::('t'::[]))))))
| OpBrand b ->
  append ('('::('O'::('p'::('B'::('r'::('a'::('n'::('d'::(' '::[])))))))))
    (append (toString coq_ToString_brands b) (')'::[]))
| OpUnbrand -> 'O'::('p'::('U'::('n'::('b'::('r'::('a'::('n'::('d'::[]))))))))
| OpCast b ->
  append ('('::('O'::('p'::('C'::('a'::('s'::('t'::(' '::[]))))))))
    (append (toString coq_ToString_brands b) (')'::[]))
| OpNatUnary aop ->
  append
    ('('::('O'::('p'::('N'::('a'::('t'::('U'::('n'::('a'::('r'::('y'::(' '::[]))))))))))))
    (append (toString coq_ToString_nat_arith_unary_op aop) (')'::[]))
| OpNatSum -> 'O'::('p'::('N'::('a'::('t'::('S'::('u'::('m'::[])))))))
| OpNatMin -> 'O'::('p'::('N'::('a'::('t'::('M'::('i'::('n'::[])))))))
| OpNatMax -> 'O'::('p'::('N'::('a'::('t'::('M'::('a'::('x'::[])))))))
| OpNatMean -> 'O'::('p'::('N'::('a'::('t'::('M'::('e'::('a'::('n'::[]))))))))
| OpFloatOfNat ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('O'::('f'::('N'::('a'::('t'::[])))))))))))
| OpFloatUnary aop ->
  append
    ('('::('O'::('p'::('F'::('l'::('o'::('a'::('t'::('U'::('n'::('a'::('r'::('y'::(' '::[]))))))))))))))
    (append (toString coq_ToString_float_arith_unary_op aop) (')'::[]))
| OpFloatTruncate ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('T'::('r'::('u'::('n'::('c'::('a'::('t'::('e'::[]))))))))))))))
| OpFloatSum ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('S'::('u'::('m'::[])))))))))
| OpFloatMean ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('M'::('e'::('a'::('n'::[]))))))))))
| OpFloatBagMin ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('B'::('a'::('g'::('M'::('i'::('n'::[]))))))))))))
| OpFloatBagMax ->
  'O'::('p'::('F'::('l'::('o'::('a'::('t'::('B'::('a'::('g'::('M'::('a'::('x'::[]))))))))))))
| OpForeignUnary fu -> toString foperators.foreign_operators_unary_tostring fu
