open Data
open ForeignData
open Lift

val unbdbool :
  foreign_data -> (bool -> bool -> bool) -> data -> data -> data option

val unudbool : foreign_data -> (bool -> bool) -> data -> data option

val unbdnat :
  foreign_data -> (int -> int -> bool) -> data -> data -> data option

val unbdata :
  foreign_data -> (data -> data -> bool) -> data -> data -> data option

val unndstring : foreign_data -> (char list -> int) -> data -> data option

val unsdstring :
  foreign_data -> (char list -> char list -> char list) -> data -> data ->
  data option

val ondcoll2 :
  foreign_data -> (data list -> data list -> 'a1) -> data -> data -> 'a1
  option

val rondcoll2 :
  foreign_data -> (data list -> data list -> data list) -> data -> data ->
  data option

val ondstring : foreign_data -> (char list -> 'a1) -> data -> 'a1 option

val ondnat : foreign_data -> (int -> 'a1) -> data -> 'a1 option

val ondfloat : foreign_data -> (float -> 'a1) -> data -> 'a1 option

val ondcoll : foreign_data -> (data list -> 'a1) -> data -> 'a1 option

val lift_oncoll :
  foreign_data -> (data list -> 'a1 option) -> data -> 'a1 option

val rondcoll : foreign_data -> (data list -> data list) -> data -> data option
