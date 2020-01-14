
type 'a coq_EqDec = 'a -> 'a -> bool

val equiv_dec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val equiv_decb : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool

val nat_eq_eqdec : int coq_EqDec

val unit_eqdec : unit coq_EqDec

val list_eqdec : 'a1 coq_EqDec -> 'a1 list coq_EqDec
