open BinInt
open Datatypes
open EquivDec
open List0

val float_eq : float -> float -> bool

val float_eq_dec : float coq_EqDec

val float_list_min : float list -> float

val float_list_max : float list -> float

val float_list_sum : float list -> float

val float_list_arithmean : float list -> float
