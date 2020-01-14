open Bag
open BinInt
open Data
open DataLift
open Datatypes
open FloatAdd
open ForeignData
open Lift
open LiftIterators
open String0

val dsum : foreign_data -> data list -> int option

val darithmean : foreign_data -> data list -> int option

val lifted_stringbag : foreign_data -> data list -> char list list option

val lifted_zbag : foreign_data -> data list -> int list option

val lifted_min : foreign_data -> data list -> data option

val lifted_max : foreign_data -> data list -> data option

val lifted_fbag : foreign_data -> data list -> float list option

val lifted_fsum : foreign_data -> data list -> data option

val lifted_farithmean : foreign_data -> data list -> data option

val lifted_fmin : foreign_data -> data list -> data option

val lifted_fmax : foreign_data -> data list -> data option

val lifted_join : foreign_data -> char list -> data list -> data option
