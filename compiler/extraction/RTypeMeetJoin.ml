open Assoc
open Bindings
open BrandRelation
open CoqLibAdd
open EquivDec
open ForeignType
open Lattice
open RType
open String0
open Sublist

(** val record_kind_rtype_join :
    record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a1)
    list -> record_kind **)

let record_kind_rtype_join k_UU2081_ k_UU2082_ l_UU2081_ l_UU2082_ =
  match k_UU2081_ with
  | Open -> Open
  | Closed ->
    (match k_UU2082_ with
     | Open -> Open
     | Closed ->
       if equiv_dec (list_eqdec string_eqdec) (domain l_UU2081_)
            (domain l_UU2082_)
       then Closed
       else Open)

(** val rtype_meet_compatible_records_dec :
    record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a2)
    list -> bool **)

let rtype_meet_compatible_records_dec k_UU2081_ k_UU2082_ l_UU2081_ l_UU2082_ =
  match k_UU2081_ with
  | Open ->
    (match k_UU2082_ with
     | Open -> true
     | Closed ->
       sublist_dec string_eqdec (domain l_UU2081_) (domain l_UU2082_))
  | Closed ->
    (match k_UU2082_ with
     | Open -> sublist_dec string_eqdec (domain l_UU2082_) (domain l_UU2081_)
     | Closed ->
       let s = sublist_dec string_eqdec (domain l_UU2081_) (domain l_UU2082_)
       in
       if s
       then sublist_dec string_eqdec (domain l_UU2082_) (domain l_UU2081_)
       else false)

(** val record_kind_rtype_meet : record_kind -> record_kind -> record_kind **)

let record_kind_rtype_meet k_UU2081_ k_UU2082_ =
  match k_UU2081_ with
  | Open -> k_UU2082_
  | Closed -> Closed

(** val rtype_join_UU2080_ :
    foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
    rtype_UU2080_ **)

let rtype_join_UU2080_ ftype br =
  let rec rtype_join_UU2080_0 _UU03c4__UU2081_ _UU03c4__UU2082_ =
    match _UU03c4__UU2081_ with
    | Bottom_UU2080_ -> _UU03c4__UU2082_
    | Top_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | _ -> Top_UU2080_)
    | Unit_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Unit_UU2080_ -> Unit_UU2080_
       | _ -> Top_UU2080_)
    | Nat_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Nat_UU2080_ -> Nat_UU2080_
       | _ -> Top_UU2080_)
    | Float_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Float_UU2080_ -> Float_UU2080_
       | _ -> Top_UU2080_)
    | Bool_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Bool_UU2080_ -> Bool_UU2080_
       | _ -> Top_UU2080_)
    | String_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | String_UU2080_ -> String_UU2080_
       | _ -> Top_UU2080_)
    | Coll_UU2080_ _UU03c4__UU2081_' ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Coll_UU2080_ _UU03c4__UU2082_' ->
         Coll_UU2080_
           (rtype_join_UU2080_0 _UU03c4__UU2081_' _UU03c4__UU2082_')
       | _ -> Top_UU2080_)
    | Rec_UU2080_ (k_UU2081_, srl) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Rec_UU2080_ (k_UU2082_, srl') ->
         Rec_UU2080_ ((record_kind_rtype_join k_UU2081_ k_UU2082_ srl srl'),
           (let rec map_rtype_join_UU2080_ l1 l2 =
              match l1 with
              | [] -> []
              | y :: srs ->
                let (s, r) = y in
                (match lookup string_dec l2 s with
                 | Some r' ->
                   (s,
                     (rtype_join_UU2080_0 r r')) :: (map_rtype_join_UU2080_
                                                      srs l2)
                 | None -> map_rtype_join_UU2080_ srs l2)
            in map_rtype_join_UU2080_ srl srl'))
       | _ -> Top_UU2080_)
    | Either_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Either_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Either_UU2080_
           ((rtype_join_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_join_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Top_UU2080_)
    | Arrow_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Arrow_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Arrow_UU2080_
           ((rtype_meet_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_join_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Top_UU2080_)
    | Brand_UU2080_ b_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Brand_UU2080_ b_UU2082_ ->
         Brand_UU2080_
           (brand_join (brand_relation_brands br) b_UU2081_ b_UU2082_)
       | _ -> Top_UU2080_)
    | Foreign_UU2080_ ft_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Foreign_UU2080_ ft_UU2082_ ->
         Foreign_UU2080_
           (ftype.foreign_type_lattice.join ft_UU2081_ ft_UU2082_)
       | _ -> Top_UU2080_)
  and rtype_meet_UU2080_0 _UU03c4__UU2081_ _UU03c4__UU2082_ =
    match _UU03c4__UU2081_ with
    | Bottom_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | _ -> Bottom_UU2080_)
    | Top_UU2080_ -> _UU03c4__UU2082_
    | Unit_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Unit_UU2080_ -> Unit_UU2080_
       | _ -> Bottom_UU2080_)
    | Nat_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Nat_UU2080_ -> Nat_UU2080_
       | _ -> Bottom_UU2080_)
    | Float_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Float_UU2080_ -> Float_UU2080_
       | _ -> Bottom_UU2080_)
    | Bool_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Bool_UU2080_ -> Bool_UU2080_
       | _ -> Bottom_UU2080_)
    | String_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | String_UU2080_ -> String_UU2080_
       | _ -> Bottom_UU2080_)
    | Coll_UU2080_ _UU03c4__UU2081_' ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Coll_UU2080_ _UU03c4__UU2082_' ->
         Coll_UU2080_
           (rtype_meet_UU2080_0 _UU03c4__UU2081_' _UU03c4__UU2082_')
       | _ -> Bottom_UU2080_)
    | Rec_UU2080_ (k_UU2081_, srl) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Rec_UU2080_ (k_UU2082_, srl') ->
         if rtype_meet_compatible_records_dec k_UU2081_ k_UU2082_ srl srl'
         then Rec_UU2080_ ((record_kind_rtype_meet k_UU2081_ k_UU2082_),
                (rec_concat_sort coq_ODT_string
                  (let rec map_rtype_meet_UU2080_ l1 l2 =
                     match l1 with
                     | [] -> []
                     | y :: srs ->
                       let (s, r) = y in
                       (match lookup string_dec l2 s with
                        | Some r' ->
                          (s,
                            (rtype_meet_UU2080_0 r r')) :: (map_rtype_meet_UU2080_
                                                             srs l2)
                        | None -> (s, r) :: (map_rtype_meet_UU2080_ srs l2))
                   in map_rtype_meet_UU2080_ srl srl')
                  (lookup_diff string_dec srl' srl)))
         else Bottom_UU2080_
       | _ -> Bottom_UU2080_)
    | Either_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Either_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Either_UU2080_
           ((rtype_meet_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_meet_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Bottom_UU2080_)
    | Arrow_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Arrow_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Arrow_UU2080_
           ((rtype_join_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_meet_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Bottom_UU2080_)
    | Brand_UU2080_ _UU03c4__UU2081_0 ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Brand_UU2080_ _UU03c4__UU2082_0 ->
         Brand_UU2080_
           (brand_meet (brand_relation_brands br) _UU03c4__UU2081_0
             _UU03c4__UU2082_0)
       | _ -> Bottom_UU2080_)
    | Foreign_UU2080_ ft_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Foreign_UU2080_ ft_UU2082_ ->
         Foreign_UU2080_
           (ftype.foreign_type_lattice.meet ft_UU2081_ ft_UU2082_)
       | _ -> Bottom_UU2080_)
  in rtype_join_UU2080_0

(** val rtype_meet_UU2080_ :
    foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
    rtype_UU2080_ **)

let rtype_meet_UU2080_ ftype br =
  let rec rtype_join_UU2080_0 _UU03c4__UU2081_ _UU03c4__UU2082_ =
    match _UU03c4__UU2081_ with
    | Bottom_UU2080_ -> _UU03c4__UU2082_
    | Top_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | _ -> Top_UU2080_)
    | Unit_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Unit_UU2080_ -> Unit_UU2080_
       | _ -> Top_UU2080_)
    | Nat_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Nat_UU2080_ -> Nat_UU2080_
       | _ -> Top_UU2080_)
    | Float_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Float_UU2080_ -> Float_UU2080_
       | _ -> Top_UU2080_)
    | Bool_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Bool_UU2080_ -> Bool_UU2080_
       | _ -> Top_UU2080_)
    | String_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | String_UU2080_ -> String_UU2080_
       | _ -> Top_UU2080_)
    | Coll_UU2080_ _UU03c4__UU2081_' ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Coll_UU2080_ _UU03c4__UU2082_' ->
         Coll_UU2080_
           (rtype_join_UU2080_0 _UU03c4__UU2081_' _UU03c4__UU2082_')
       | _ -> Top_UU2080_)
    | Rec_UU2080_ (k_UU2081_, srl) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Rec_UU2080_ (k_UU2082_, srl') ->
         Rec_UU2080_ ((record_kind_rtype_join k_UU2081_ k_UU2082_ srl srl'),
           (let rec map_rtype_join_UU2080_ l1 l2 =
              match l1 with
              | [] -> []
              | y :: srs ->
                let (s, r) = y in
                (match lookup string_dec l2 s with
                 | Some r' ->
                   (s,
                     (rtype_join_UU2080_0 r r')) :: (map_rtype_join_UU2080_
                                                      srs l2)
                 | None -> map_rtype_join_UU2080_ srs l2)
            in map_rtype_join_UU2080_ srl srl'))
       | _ -> Top_UU2080_)
    | Either_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Either_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Either_UU2080_
           ((rtype_join_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_join_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Top_UU2080_)
    | Arrow_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Arrow_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Arrow_UU2080_
           ((rtype_meet_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_join_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Top_UU2080_)
    | Brand_UU2080_ b_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Brand_UU2080_ b_UU2082_ ->
         Brand_UU2080_
           (brand_join (brand_relation_brands br) b_UU2081_ b_UU2082_)
       | _ -> Top_UU2080_)
    | Foreign_UU2080_ ft_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Bottom_UU2080_ -> _UU03c4__UU2081_
       | Foreign_UU2080_ ft_UU2082_ ->
         Foreign_UU2080_
           (ftype.foreign_type_lattice.join ft_UU2081_ ft_UU2082_)
       | _ -> Top_UU2080_)
  and rtype_meet_UU2080_0 _UU03c4__UU2081_ _UU03c4__UU2082_ =
    match _UU03c4__UU2081_ with
    | Bottom_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | _ -> Bottom_UU2080_)
    | Top_UU2080_ -> _UU03c4__UU2082_
    | Unit_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Unit_UU2080_ -> Unit_UU2080_
       | _ -> Bottom_UU2080_)
    | Nat_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Nat_UU2080_ -> Nat_UU2080_
       | _ -> Bottom_UU2080_)
    | Float_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Float_UU2080_ -> Float_UU2080_
       | _ -> Bottom_UU2080_)
    | Bool_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Bool_UU2080_ -> Bool_UU2080_
       | _ -> Bottom_UU2080_)
    | String_UU2080_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | String_UU2080_ -> String_UU2080_
       | _ -> Bottom_UU2080_)
    | Coll_UU2080_ _UU03c4__UU2081_' ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Coll_UU2080_ _UU03c4__UU2082_' ->
         Coll_UU2080_
           (rtype_meet_UU2080_0 _UU03c4__UU2081_' _UU03c4__UU2082_')
       | _ -> Bottom_UU2080_)
    | Rec_UU2080_ (k_UU2081_, srl) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Rec_UU2080_ (k_UU2082_, srl') ->
         if rtype_meet_compatible_records_dec k_UU2081_ k_UU2082_ srl srl'
         then Rec_UU2080_ ((record_kind_rtype_meet k_UU2081_ k_UU2082_),
                (rec_concat_sort coq_ODT_string
                  (let rec map_rtype_meet_UU2080_ l1 l2 =
                     match l1 with
                     | [] -> []
                     | y :: srs ->
                       let (s, r) = y in
                       (match lookup string_dec l2 s with
                        | Some r' ->
                          (s,
                            (rtype_meet_UU2080_0 r r')) :: (map_rtype_meet_UU2080_
                                                             srs l2)
                        | None -> (s, r) :: (map_rtype_meet_UU2080_ srs l2))
                   in map_rtype_meet_UU2080_ srl srl')
                  (lookup_diff string_dec srl' srl)))
         else Bottom_UU2080_
       | _ -> Bottom_UU2080_)
    | Either_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Either_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Either_UU2080_
           ((rtype_meet_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_meet_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Bottom_UU2080_)
    | Arrow_UU2080_ (_UU03c4_l_UU2081_, _UU03c4_r_UU2081_) ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Arrow_UU2080_ (_UU03c4_l_UU2082_, _UU03c4_r_UU2082_) ->
         Arrow_UU2080_
           ((rtype_join_UU2080_0 _UU03c4_l_UU2081_ _UU03c4_l_UU2082_),
           (rtype_meet_UU2080_0 _UU03c4_r_UU2081_ _UU03c4_r_UU2082_))
       | _ -> Bottom_UU2080_)
    | Brand_UU2080_ _UU03c4__UU2081_0 ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Brand_UU2080_ _UU03c4__UU2082_0 ->
         Brand_UU2080_
           (brand_meet (brand_relation_brands br) _UU03c4__UU2081_0
             _UU03c4__UU2082_0)
       | _ -> Bottom_UU2080_)
    | Foreign_UU2080_ ft_UU2081_ ->
      (match _UU03c4__UU2082_ with
       | Top_UU2080_ -> _UU03c4__UU2081_
       | Foreign_UU2080_ ft_UU2082_ ->
         Foreign_UU2080_
           (ftype.foreign_type_lattice.meet ft_UU2081_ ft_UU2082_)
       | _ -> Bottom_UU2080_)
  in rtype_meet_UU2080_0

(** val rtype_join :
    foreign_type -> brand_relation -> rtype -> rtype -> rtype **)

let rtype_join =
  rtype_join_UU2080_

(** val rtype_meet :
    foreign_type -> brand_relation -> rtype -> rtype -> rtype **)

let rtype_meet =
  rtype_meet_UU2080_
