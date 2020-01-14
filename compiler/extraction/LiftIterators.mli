open Datatypes
open Lift

val lift_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val lift_flat_map : ('a1 -> 'a2 list option) -> 'a1 list -> 'a2 list option
