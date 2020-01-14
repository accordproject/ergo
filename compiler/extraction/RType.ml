open Assoc
open Bindings
open BrandRelation
open CoqLibAdd
open Datatypes
open EquivDec
open ForeignType
open List0
open SortingAdd
open String0

type record_kind =
| Open
| Closed

(** val record_kind_eqdec : record_kind coq_EqDec **)

let record_kind_eqdec x y =
  match x with
  | Open -> (match y with
             | Open -> true
             | Closed -> false)
  | Closed -> (match y with
               | Open -> false
               | Closed -> true)

type rtype_UU2080_ =
| Bottom_UU2080_
| Top_UU2080_
| Unit_UU2080_
| Nat_UU2080_
| Float_UU2080_
| Bool_UU2080_
| String_UU2080_
| Coll_UU2080_ of rtype_UU2080_
| Rec_UU2080_ of record_kind * (char list * rtype_UU2080_) list
| Either_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Arrow_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Brand_UU2080_ of brands
| Foreign_UU2080_ of foreign_type_type

(** val rtype_UU2080__eqdec : foreign_type -> rtype_UU2080_ coq_EqDec **)

let rec rtype_UU2080__eqdec ftype x y =
  match x with
  | Bottom_UU2080_ -> (match y with
                       | Bottom_UU2080_ -> true
                       | _ -> false)
  | Top_UU2080_ -> (match y with
                    | Top_UU2080_ -> true
                    | _ -> false)
  | Unit_UU2080_ -> (match y with
                     | Unit_UU2080_ -> true
                     | _ -> false)
  | Nat_UU2080_ -> (match y with
                    | Nat_UU2080_ -> true
                    | _ -> false)
  | Float_UU2080_ -> (match y with
                      | Float_UU2080_ -> true
                      | _ -> false)
  | Bool_UU2080_ -> (match y with
                     | Bool_UU2080_ -> true
                     | _ -> false)
  | String_UU2080_ -> (match y with
                       | String_UU2080_ -> true
                       | _ -> false)
  | Coll_UU2080_ x0 ->
    (match y with
     | Coll_UU2080_ y0 -> rtype_UU2080__eqdec ftype x0 y0
     | _ -> false)
  | Rec_UU2080_ (k, x0) ->
    (match y with
     | Rec_UU2080_ (k0, srl) ->
       let s = equiv_dec record_kind_eqdec k k0 in
       if s
       then list_Forallt_eq_dec x0 srl
              (forallt_impl x0
                (let rec frec = function
                 | [] -> Forallt_nil
                 | sd :: c0 ->
                   Forallt_cons (sd, c0,
                     (rtype_UU2080__eqdec ftype (snd sd)), (frec c0))
                 in frec x0)
                (forallt_weaken (fun x1 h y0 ->
                  let (s0, r) = x1 in
                  let (s1, r0) = y0 in
                  pair_eq_dec s0 r s1 r0 (string_dec s0 s1) (h r0)) x0))
       else false
     | _ -> false)
  | Either_UU2080_ (l, r) ->
    (match y with
     | Either_UU2080_ (y1, y2) ->
       let s = rtype_UU2080__eqdec ftype l y1 in
       if s then rtype_UU2080__eqdec ftype r y2 else false
     | _ -> false)
  | Arrow_UU2080_ (tin, tout) ->
    (match y with
     | Arrow_UU2080_ (y1, y2) ->
       let s = rtype_UU2080__eqdec ftype tin y1 in
       if s then rtype_UU2080__eqdec ftype tout y2 else false
     | _ -> false)
  | Brand_UU2080_ b ->
    (match y with
     | Brand_UU2080_ b0 -> equiv_dec (list_eqdec string_eqdec) b b0
     | _ -> false)
  | Foreign_UU2080_ ft ->
    (match y with
     | Foreign_UU2080_ ft0 -> ftype.foreign_type_dec ft ft0
     | _ -> false)

type rtype = rtype_UU2080_

(** val rtype_eq_dec : foreign_type -> brand_relation -> rtype coq_EqDec **)

let rtype_eq_dec ftype _ x y =
  equiv_dec (rtype_UU2080__eqdec ftype) x y

(** val coq_Bottom : foreign_type -> brand_relation -> rtype **)

let coq_Bottom _ _ =
  Bottom_UU2080_

(** val coq_Top : foreign_type -> brand_relation -> rtype **)

let coq_Top _ _ =
  Top_UU2080_

(** val coq_Unit : foreign_type -> brand_relation -> rtype **)

let coq_Unit _ _ =
  Unit_UU2080_

(** val coq_Nat : foreign_type -> brand_relation -> rtype **)

let coq_Nat _ _ =
  Nat_UU2080_

(** val coq_Float : foreign_type -> brand_relation -> rtype **)

let coq_Float _ _ =
  Float_UU2080_

(** val coq_Bool : foreign_type -> brand_relation -> rtype **)

let coq_Bool _ _ =
  Bool_UU2080_

(** val coq_String : foreign_type -> brand_relation -> rtype **)

let coq_String _ _ =
  String_UU2080_

(** val coq_Coll : foreign_type -> brand_relation -> rtype -> rtype **)

let coq_Coll _ _ _UU03c4_ =
  Coll_UU2080_ _UU03c4_

(** val coq_Either :
    foreign_type -> brand_relation -> rtype -> rtype -> rtype **)

let coq_Either _ _ _UU03c4_l _UU03c4_r =
  Either_UU2080_ (_UU03c4_l, _UU03c4_r)

(** val coq_Arrow :
    foreign_type -> brand_relation -> rtype -> rtype -> rtype **)

let coq_Arrow _ _ _UU03c4_l _UU03c4_r =
  Arrow_UU2080_ (_UU03c4_l, _UU03c4_r)

(** val coq_Foreign :
    foreign_type -> brand_relation -> foreign_type_type -> rtype **)

let coq_Foreign _ _ ft =
  Foreign_UU2080_ ft

(** val coq_Rec :
    foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
    -> rtype **)

let coq_Rec _ _ k srl =
  Rec_UU2080_ (k, (map (fun x -> ((fst x), (snd x))) srl))

(** val coq_Brand : foreign_type -> brand_relation -> brands -> rtype **)

let coq_Brand _ br b =
  Brand_UU2080_ (canon_brands (brand_relation_brands br) b)

(** val coq_Option : foreign_type -> brand_relation -> rtype -> rtype **)

let coq_Option ftype br _UU03c4_ =
  coq_Either ftype br _UU03c4_ (coq_Unit ftype br)

(** val from_Rec_UU2080_ :
    foreign_type -> brand_relation -> record_kind ->
    (char list * rtype_UU2080_) list -> (char list * rtype_UU2080_) list **)

let rec from_Rec_UU2080_ ftype br k = function
| [] -> []
| y :: l0 ->
  let s = from_Rec_UU2080_ ftype br k l0 in let (s0, r) = y in (s0, r) :: s

(** val coq_RecMaybe :
    foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
    -> rtype option **)

let coq_RecMaybe ftype br k lsr0 =
  if is_list_sorted coq_ODT_string.coq_ODT_lt_dec (domain lsr0)
  then Some (coq_Rec ftype br k lsr0)
  else None
