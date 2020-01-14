open Assoc
open Bindings
open CoqLibAdd
open ForeignType
open RType
open Sublist
open TBrandModel

(** val tdot : (char list * 'a1) list -> char list -> 'a1 option **)

let tdot =
  edot

(** val tuneither :
    foreign_type -> brand_model -> rtype -> (rtype * rtype) option **)

let tuneither _ _ = function
| Either_UU2080_ (x1, x2) -> Some (x1, x2)
| _ -> None

(** val tuncoll : foreign_type -> brand_model -> rtype -> rtype option **)

let tuncoll _ _ = function
| Coll_UU2080_ x -> Some x
| _ -> None

(** val tsingleton : foreign_type -> brand_model -> rtype -> rtype option **)

let tsingleton ftype m = function
| Coll_UU2080_ x -> Some (coq_Option ftype m.brand_model_relation x)
| _ -> None

(** val tunrec :
    foreign_type -> brand_model -> rtype ->
    (record_kind * (char list * rtype) list) option **)

let tunrec ftype m = function
| Rec_UU2080_ (k, srl) ->
  let h = from_Rec_UU2080_ ftype m.brand_model_relation k srl in Some (k, h)
| _ -> None

(** val trecConcatRight :
    foreign_type -> brand_model -> rtype -> rtype -> rtype option **)

let trecConcatRight ftype m _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match _UU03c4__UU2081_ with
  | Rec_UU2080_ (k, srl) ->
    (match _UU03c4__UU2082_ with
     | Rec_UU2080_ (k0, srl0) ->
       let h = from_Rec_UU2080_ ftype m.brand_model_relation k srl in
       let h0 = from_Rec_UU2080_ ftype m.brand_model_relation k0 srl0 in
       (match k0 with
        | Open -> None
        | Closed ->
          let h1 = rec_concat_sort coq_ODT_string h h0 in
          coq_RecMaybe ftype m.brand_model_relation k h1)
     | _ -> None)
  | _ -> None

(** val tmergeConcat :
    foreign_type -> brand_model -> rtype -> rtype -> rtype option **)

let tmergeConcat ftype m _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match _UU03c4__UU2081_ with
  | Rec_UU2080_ (k, srl) ->
    (match _UU03c4__UU2082_ with
     | Rec_UU2080_ (k0, srl0) ->
       let h = from_Rec_UU2080_ ftype m.brand_model_relation k srl in
       let h0 = from_Rec_UU2080_ ftype m.brand_model_relation k0 srl0 in
       let h1 =
         merge_bindings (rtype_eq_dec ftype m.brand_model_relation) h h0
       in
       (match h1 with
        | Some rSome ->
          (match k with
           | Open ->
             (match k0 with
              | Open -> coq_RecMaybe ftype m.brand_model_relation Open rSome
              | Closed -> None)
           | Closed ->
             (match k0 with
              | Open -> None
              | Closed ->
                coq_RecMaybe ftype m.brand_model_relation Closed rSome))
        | None -> None)
     | _ -> None)
  | _ -> None

(** val tunrecdot :
    foreign_type -> brand_model -> char list -> rtype -> rtype option **)

let tunrecdot ftype m s _UU03c4_ =
  let h = tunrec ftype m _UU03c4_ in
  (match h with
   | Some p -> let (_, l) = p in tdot l s
   | None -> None)

(** val tunrecremove :
    foreign_type -> brand_model -> char list -> rtype -> rtype option **)

let tunrecremove ftype m s _UU03c4_ =
  let h = tunrec ftype m _UU03c4_ in
  (match h with
   | Some p ->
     let (r, l) = p in
     coq_RecMaybe ftype m.brand_model_relation r (rremove l s)
   | None -> None)

(** val tunrecproject :
    foreign_type -> brand_model -> char list list -> rtype -> rtype option **)

let tunrecproject ftype m sl _UU03c4_ =
  let h = tunrec ftype m _UU03c4_ in
  (match h with
   | Some p ->
     let (_, l) = p in
     let s = sublist_dec string_eqdec sl (domain l) in
     if s
     then coq_RecMaybe ftype m.brand_model_relation Closed (rproject l sl)
     else None
   | None -> None)
