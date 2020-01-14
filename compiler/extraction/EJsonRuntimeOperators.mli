open BrandRelation
open CoqLibAdd
open EJson
open EmitUtil
open Encode
open ForeignEJson
open ForeignEJsonRuntime
open List0
open String0
open ToString

type 'foreign_ejson_runtime_op ejson_runtime_op =
| EJsonRuntimeEqual
| EJsonRuntimeCompare
| EJsonRuntimeToString
| EJsonRuntimeToText
| EJsonRuntimeRecConcat
| EJsonRuntimeRecMerge
| EJsonRuntimeRecRemove
| EJsonRuntimeRecProject
| EJsonRuntimeRecDot
| EJsonRuntimeArray
| EJsonRuntimeArrayLength
| EJsonRuntimeArrayPush
| EJsonRuntimeArrayAccess
| EJsonRuntimeEither
| EJsonRuntimeToLeft
| EJsonRuntimeToRight
| EJsonRuntimeUnbrand
| EJsonRuntimeCast
| EJsonRuntimeDistinct
| EJsonRuntimeSingleton
| EJsonRuntimeFlatten
| EJsonRuntimeUnion
| EJsonRuntimeMinus
| EJsonRuntimeMin
| EJsonRuntimeMax
| EJsonRuntimeNth
| EJsonRuntimeCount
| EJsonRuntimeContains
| EJsonRuntimeSort
| EJsonRuntimeGroupBy
| EJsonRuntimeLength
| EJsonRuntimeSubstring
| EJsonRuntimeSubstringEnd
| EJsonRuntimeStringJoin
| EJsonRuntimeLike
| EJsonRuntimeNatLt
| EJsonRuntimeNatLe
| EJsonRuntimeNatPlus
| EJsonRuntimeNatMinus
| EJsonRuntimeNatMult
| EJsonRuntimeNatDiv
| EJsonRuntimeNatRem
| EJsonRuntimeNatAbs
| EJsonRuntimeNatLog2
| EJsonRuntimeNatSqrt
| EJsonRuntimeNatMinPair
| EJsonRuntimeNatMaxPair
| EJsonRuntimeNatSum
| EJsonRuntimeNatMin
| EJsonRuntimeNatMax
| EJsonRuntimeNatArithMean
| EJsonRuntimeFloatOfNat
| EJsonRuntimeFloatSum
| EJsonRuntimeFloatArithMean
| EJsonRuntimeFloatMin
| EJsonRuntimeFloatMax
| EJsonRuntimeNatOfFloat
| EJsonRuntimeForeign of 'foreign_ejson_runtime_op

val string_of_ejson_runtime_op :
  'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> 'a2
  ejson_runtime_op -> char list

val defaultEJsonToString : 'a1 foreign_ejson -> 'a1 ejson -> char list
