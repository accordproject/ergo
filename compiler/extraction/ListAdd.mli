open EquivDec
open List0

val coq_Forall_dec_defined : ('a1 -> bool) -> 'a1 list -> bool

val incl_list_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val coq_NoDup_dec : 'a1 coq_EqDec -> 'a1 list -> bool

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option
