open BinInt
open EquivDec
open List0
open String0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val forall_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool **)

let rec forall_in_dec l dec =
  match l with
  | [] -> true
  | y :: l0 ->
    let s = dec y __ in
    if s then forall_in_dec l0 (fun x _ -> dec x __) else false

(** val exists_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool **)

let rec exists_in_dec l dec =
  match l with
  | [] -> false
  | y :: l0 ->
    let s = dec y __ in
    if s then true else exists_in_dec l0 (fun x _ -> dec x __)

type ('a, 'p) coq_Forallt =
| Forallt_nil
| Forallt_cons of 'a * 'a list * 'p * ('a, 'p) coq_Forallt

(** val list_Forallt_eq_dec :
    'a1 list -> 'a1 list -> ('a1, 'a1 -> bool) coq_Forallt -> bool **)

let rec list_Forallt_eq_dec c l x =
  match c with
  | [] -> (match l with
           | [] -> true
           | _ :: _ -> false)
  | _ :: l0 ->
    (match l with
     | [] -> false
     | a0 :: l1 ->
       (match x with
        | Forallt_nil -> assert false (* absurd case *)
        | Forallt_cons (_, _, x0, x1) ->
          let s = x0 a0 in if s then list_Forallt_eq_dec l0 l1 x1 else false))

(** val forallt_impl :
    'a1 list -> ('a1, 'a2) coq_Forallt -> ('a1, 'a2 -> 'a3) coq_Forallt ->
    ('a1, 'a3) coq_Forallt **)

let rec forallt_impl l x x0 =
  match l with
  | [] -> Forallt_nil
  | y :: l0 ->
    (match x with
     | Forallt_nil -> assert false (* absurd case *)
     | Forallt_cons (_, _, x1, x2) ->
       (match x0 with
        | Forallt_nil -> assert false (* absurd case *)
        | Forallt_cons (_, _, x3, x4) ->
          Forallt_cons (y, l0, (x3 x1), (forallt_impl l0 x2 x4))))

(** val forallt_weaken :
    ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a2) coq_Forallt **)

let rec forallt_weaken x = function
| [] -> Forallt_nil
| y :: l0 -> Forallt_cons (y, l0, (x y), (forallt_weaken x l0))

(** val coq_Forallt_In :
    'a1 list -> 'a1 coq_EqDec -> ('a1, 'a2) coq_Forallt -> 'a1 -> 'a2 **)

let rec coq_Forallt_In _ eq x a =
  match x with
  | Forallt_nil -> assert false (* absurd case *)
  | Forallt_cons (x0, l, y, f) ->
    let s = equiv_dec eq x0 a in
    if s
    then y
    else let s0 = in_dec eq a l in
         if s0
         then coq_Forallt_In l eq f a
         else assert false (* absurd case *)

(** val pair_eq_dec : 'a1 -> 'a2 -> 'a1 -> 'a2 -> bool -> bool -> bool **)

let pair_eq_dec _ _ _ _ h h0 =
  if h then h0 else false

(** val string_eqdec : char list coq_EqDec **)

let string_eqdec =
  string_dec

(** val pair_eqdec :
    'a1 coq_EqDec -> 'a2 coq_EqDec -> ('a1 * 'a2) coq_EqDec **)

let pair_eqdec h h0 x y =
  let (a, b) = x in
  let (a0, b0) = y in pair_eq_dec a b a0 b0 (h a a0) (h0 b b0)

(** val option_eqdec : 'a1 coq_EqDec -> 'a1 option coq_EqDec **)

let option_eqdec h x y =
  match x with
  | Some a -> (match y with
               | Some a0 -> equiv_dec h a a0
               | None -> false)
  | None -> (match y with
             | Some _ -> false
             | None -> true)

(** val coq_ZToSignedNat : int -> bool * int **)

let coq_ZToSignedNat z =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> (true, (Z.to_nat z)))
    (fun _ -> (true, (Z.to_nat z)))
    (fun p ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun _ -> (true, (Z.to_nat z)))
      (fun _ -> (true, (Z.to_nat z)))
      (fun _ -> (false, (Z.to_nat z)))
      p)
    (Z.sgn z)

(** val is_true : bool -> bool **)

let is_true = function
| true -> true
| false -> false

type 'a coq_ToString =
  'a -> char list
  (* singleton inductive, whose constructor was Build_ToString *)

(** val toString : 'a1 coq_ToString -> 'a1 -> char list **)

let toString toString0 =
  toString0
