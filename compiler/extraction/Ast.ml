open CoqLibAdd
open Names
open Provenance
open QLib
open String0

type 'a import_decl =
| ImportAll of 'a * namespace_name
| ImportSelf of 'a * namespace_name
| ImportName of 'a * namespace_name * local_name

(** val import_annot : 'a1 import_decl -> 'a1 **)

let import_annot = function
| ImportAll (a, _) -> a
| ImportSelf (a, _) -> a
| ImportName (a, _, _) -> a

type 'n extends = 'n option

type limport_decl = provenance import_decl

type rextends = relative_name extends

type aextends = absolute_name extends

type is_abstract = bool

type 'n type_annotation = 'n option

type ('a, 'n) ergo_pattern =
| CaseData of 'a * QcertData.data
| CaseEnum of 'a * 'n
| CaseWildcard of 'a * 'n type_annotation
| CaseLet of 'a * char list * 'n type_annotation
| CaseLetOption of 'a * char list * 'n type_annotation

type lrergo_pattern = (provenance, relative_name) ergo_pattern

type laergo_pattern = (provenance, absolute_name) ergo_pattern

type ergo_unary_operator =
| EOpUMinus
| EOpDot of char list

(** val coq_ToString_ergo_unary_operator :
    ergo_unary_operator coq_ToString **)

let coq_ToString_ergo_unary_operator = function
| EOpUMinus -> '-'::[]
| EOpDot a -> append ('.'::[]) a

type ergo_binary_operator =
| EOpPlus
| EOpMinus
| EOpMultiply
| EOpDivide
| EOpRemainder
| EOpGe
| EOpGt
| EOpLe
| EOpLt

(** val coq_ToString_ergo_binary_operator :
    ergo_binary_operator coq_ToString **)

let coq_ToString_ergo_binary_operator = function
| EOpPlus -> '+'::[]
| EOpMinus -> '-'::[]
| EOpMultiply -> '*'::[]
| EOpDivide -> '/'::[]
| EOpRemainder -> '%'::[]
| EOpGe -> '>'::('='::[])
| EOpGt -> '>'::[]
| EOpLe -> '<'::('='::[])
| EOpLt -> '<'::[]
