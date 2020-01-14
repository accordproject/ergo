open BinInt
open Bool
open BrandRelation
open CoqLibAdd
open Datatypes
open EquivDec
open FloatAdd
open ForeignData
open String0

type data =
| Coq_dunit
| Coq_dnat of int
| Coq_dfloat of float
| Coq_dbool of bool
| Coq_dstring of char list
| Coq_dcoll of data list
| Coq_drec of (char list * data) list
| Coq_dleft of data
| Coq_dright of data
| Coq_dbrand of brands * data
| Coq_dforeign of foreign_data_model

val data_eq_dec : foreign_data -> data -> data -> bool

val data_eqdec : foreign_data -> data coq_EqDec

val dsome : foreign_data -> data -> data

val dnone : foreign_data -> data
