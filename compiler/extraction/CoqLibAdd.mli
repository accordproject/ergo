open BinInt
open EquivDec
open List0
open String0

type __ = Obj.t

val forall_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool

val exists_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool

type ('a, 'p) coq_Forallt =
| Forallt_nil
| Forallt_cons of 'a * 'a list * 'p * ('a, 'p) coq_Forallt

val list_Forallt_eq_dec :
  'a1 list -> 'a1 list -> ('a1, 'a1 -> bool) coq_Forallt -> bool

val forallt_impl :
  'a1 list -> ('a1, 'a2) coq_Forallt -> ('a1, 'a2 -> 'a3) coq_Forallt ->
  ('a1, 'a3) coq_Forallt

val forallt_weaken : ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a2) coq_Forallt

val coq_Forallt_In :
  'a1 list -> 'a1 coq_EqDec -> ('a1, 'a2) coq_Forallt -> 'a1 -> 'a2

val pair_eq_dec : 'a1 -> 'a2 -> 'a1 -> 'a2 -> bool -> bool -> bool

val string_eqdec : char list coq_EqDec

val pair_eqdec : 'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) coq_EqDec

val option_eqdec : 'a1 coq_EqDec -> 'a1 option coq_EqDec

val coq_ZToSignedNat : int -> bool * int

val is_true : bool -> bool

type 'a coq_ToString =
  'a -> char list
  (* singleton inductive, whose constructor was Build_ToString *)

val toString : 'a1 coq_ToString -> 'a1 -> char list
