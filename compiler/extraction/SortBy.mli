open Bindings
open Data
open ForeignData
open Lift
open LiftIterators
open SortingDesc

val get_criteria : foreign_data -> data -> coq_SortCriteria -> sdata option

val get_criterias :
  foreign_data -> data -> coq_SortCriterias -> sdata list option

val sortable_data_of_data :
  foreign_data -> data -> coq_SortCriterias -> data sortable_data option

val sortable_coll_of_coll :
  foreign_data -> coq_SortCriterias -> data list -> data sortable_data list
  option

val data_sort : foreign_data -> coq_SortCriterias -> data -> data option
