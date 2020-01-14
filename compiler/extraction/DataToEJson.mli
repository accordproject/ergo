open Data
open Datatypes
open EJson
open Encode
open ForeignDataToEJson
open ForeignEJson
open ForeignRuntime
open List0
open SortingDesc

val data_to_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson -> data
  -> 'a1 ejson

val sortCriteria_to_ejson : (char list * coq_SortDesc) -> 'a1 ejson
