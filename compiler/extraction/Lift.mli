open EquivDec

val lift : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val olift : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val lift2 : ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option

val mk_lazy_lift :
  'a1 coq_EqDec -> ('a2 -> 'a1 -> 'a1 -> 'a2) -> 'a2 -> 'a1 -> 'a1 -> 'a2
