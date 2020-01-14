open Bindings
open Data
open ForeignData
open Lift
open LiftIterators
open SortingDesc

(** val get_criteria :
    foreign_data -> data -> coq_SortCriteria -> sdata option **)

let get_criteria _ d = function
| (att, _) ->
  (match d with
   | Coq_drec r ->
     (match edot r att with
      | Some d0 ->
        (match d0 with
         | Coq_dnat n -> Some (Coq_sdnat n)
         | Coq_dstring s -> Some (Coq_sdstring s)
         | _ -> None)
      | None -> None)
   | _ -> None)

(** val get_criterias :
    foreign_data -> data -> coq_SortCriterias -> sdata list option **)

let get_criterias fdata d scl =
  lift_map (get_criteria fdata d) scl

(** val sortable_data_of_data :
    foreign_data -> data -> coq_SortCriterias -> data sortable_data option **)

let sortable_data_of_data fdata d scl =
  lift (fun c -> (c, d)) (get_criterias fdata d scl)

(** val sortable_coll_of_coll :
    foreign_data -> coq_SortCriterias -> data list -> data sortable_data list
    option **)

let sortable_coll_of_coll fdata scl coll =
  lift_map (fun d -> sortable_data_of_data fdata d scl) coll

(** val data_sort :
    foreign_data -> coq_SortCriterias -> data -> data option **)

let data_sort fdata scl = function
| Coq_dcoll coll ->
  lift (fun x -> Coq_dcoll x)
    (lift coll_of_sortable_coll
      (lift sort_sortable_coll (sortable_coll_of_coll fdata scl coll)))
| _ -> None
