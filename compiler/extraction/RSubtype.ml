open Assoc
open BrandRelation
open CoqLibAdd
open Datatypes
open ForeignType
open List0
open ListAdd
open RType
open String0

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val subtype_both_dec :
    foreign_type -> brand_relation -> rtype -> rtype -> bool * bool **)

let subtype_both_dec ftype br x y =
  let rec f = function
  | Bottom_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (true, true)
      | _ -> (true, false))
  | Top_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Top_UU2080_ -> (true, true)
      | _ -> (false, true))
  | Unit_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Unit_UU2080_ -> (true, true)
      | _ -> (false, false))
  | Nat_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Nat_UU2080_ -> (true, true)
      | _ -> (false, false))
  | Float_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Float_UU2080_ -> (true, true)
      | _ -> (false, false))
  | Bool_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Bool_UU2080_ -> (true, true)
      | _ -> (false, false))
  | String_UU2080_ ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | String_UU2080_ -> (true, true)
      | _ -> (false, false))
  | Coll_UU2080_ x0 ->
    let iHx = f x0 in
    (fun _ y0 ->
    match y0 with
    | Bottom_UU2080_ -> (false, true)
    | Top_UU2080_ -> (true, false)
    | Coll_UU2080_ y1 ->
      ((let p = iHx __ y1 in let (s, _) = p in s),
        (let p = iHx __ y1 in let (_, s) = p in s))
    | _ -> (false, false))
  | Rec_UU2080_ (k, x0) ->
    let h =
      let rec frec = function
      | [] -> Forallt_nil
      | sd :: c0 -> Forallt_cons (sd, c0, (f (snd sd)), (frec c0))
      in frec x0
    in
    (fun _ y0 ->
    match y0 with
    | Bottom_UU2080_ -> (false, true)
    | Top_UU2080_ -> (true, false)
    | Rec_UU2080_ (k0, srl) ->
      ((let sub =
          let rec f0 = function
          | [] -> true
          | y1 :: l0 ->
            let (s, r) = y1 in
            (match lookup string_dec x0 s with
             | Some r0 ->
               let p =
                 coq_Forallt_In x0
                   (pair_eqdec string_eqdec (rtype_UU2080__eqdec ftype)) h
                   (s, r0) __ r
               in
               let (s0, _) = p in if s0 then f0 l0 else false
             | None -> false)
          in f0 srl
        in
        if sub
        then (match k0 with
              | Open -> true
              | Closed ->
                (match k with
                 | Open -> false
                 | Closed -> incl_list_dec string_dec (domain x0) (domain srl)))
        else false),
        (let sub =
           let rec f0 l h0 =
             match l with
             | [] -> true
             | y1 :: l0 ->
               let (s, _) = y1 in
               (match lookup string_dec srl s with
                | Some r0 ->
                  (match h0 with
                   | Forallt_nil -> assert false (* absurd case *)
                   | Forallt_cons (_, _, h1, h2) ->
                     let p = h1 __ r0 in
                     let (_, issub) = p in if issub then f0 l0 h2 else false)
                | None -> false)
           in f0 x0 h
         in
         if sub
         then (match k with
               | Open -> true
               | Closed ->
                 (match k0 with
                  | Open -> false
                  | Closed ->
                    incl_list_dec string_dec (domain srl) (domain x0)))
         else false))
    | _ -> (false, false))
  | Either_UU2080_ (l, r) ->
    let iHx1 = f l in
    let iHx2 = f r in
    (fun _ y0 ->
    match y0 with
    | Bottom_UU2080_ -> (false, true)
    | Top_UU2080_ -> (true, false)
    | Either_UU2080_ (y1, y2) ->
      ((let p = iHx1 __ y1 in
        let (s, _) = p in
        if s then let p0 = iHx2 __ y2 in let (s0, _) = p0 in s0 else false),
        (let p = iHx1 __ y1 in
         let (_, s) = p in
         if s then let p0 = iHx2 __ y2 in let (_, s0) = p0 in s0 else false))
    | _ -> (false, false))
  | Arrow_UU2080_ (tin, tout) ->
    let iHx1 = f tin in
    let iHx2 = f tout in
    (fun _ y0 ->
    match y0 with
    | Bottom_UU2080_ -> (false, true)
    | Top_UU2080_ -> (true, false)
    | Arrow_UU2080_ (y1, y2) ->
      ((let p = iHx1 __ y1 in
        let (_, s0) = p in
        if s0 then let p0 = iHx2 __ y2 in let (s1, _) = p0 in s1 else false),
        (let p = iHx1 __ y1 in
         let (s, _) = p in
         if s then let p0 = iHx2 __ y2 in let (_, s2) = p0 in s2 else false))
    | _ -> (false, false))
  | Brand_UU2080_ b ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Brand_UU2080_ b0 ->
        ((sub_brands_dec (brand_relation_brands br) b b0),
          (sub_brands_dec (brand_relation_brands br) b0 b))
      | _ -> (false, false))
  | Foreign_UU2080_ ft ->
    (fun _ y0 ->
      match y0 with
      | Bottom_UU2080_ -> (false, true)
      | Top_UU2080_ -> (true, false)
      | Foreign_UU2080_ ft0 ->
        ((ftype.foreign_type_sub_dec ft ft0),
          (ftype.foreign_type_sub_dec ft0 ft))
      | _ -> (false, false))
  in f x __ y

(** val subtype_dec :
    foreign_type -> brand_relation -> rtype -> rtype -> bool **)

let subtype_dec ftype br x y =
  let p = subtype_both_dec ftype br x y in let (s, _) = p in s

(** val check_subtype_pairs :
    foreign_type -> brand_relation -> (rtype * rtype) list -> bool **)

let check_subtype_pairs ftype br l =
  forallb (fun _UU03c4_s ->
    if subtype_dec ftype br (fst _UU03c4_s) (snd _UU03c4_s)
    then true
    else false) l

(** val enforce_unary_op_schema :
    foreign_type -> brand_relation -> (rtype * rtype) -> rtype ->
    (rtype * rtype) option **)

let enforce_unary_op_schema ftype br ts1 tr =
  if check_subtype_pairs ftype br (ts1 :: [])
  then Some (tr, (snd ts1))
  else None

(** val enforce_binary_op_schema :
    foreign_type -> brand_relation -> (rtype * rtype) -> (rtype * rtype) ->
    rtype -> ((rtype * rtype) * rtype) option **)

let enforce_binary_op_schema ftype br ts1 ts2 tr =
  if check_subtype_pairs ftype br (ts1 :: (ts2 :: []))
  then Some ((tr, (snd ts1)), (snd ts2))
  else None
