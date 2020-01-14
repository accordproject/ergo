open BinNat
open BinPos
open Datatypes

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val sgn : int -> int **)

  let sgn z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun _ -> 1)
      (fun _ -> (~-) 1)
      z

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val min : int -> int -> int **)

  let min = Pervasives.min

  (** val abs : int -> int **)

  let abs = Pervasives.abs

  (** val to_nat : int -> int **)

  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun _ -> 0)
      z

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Pos.of_succ_nat n0))
      n

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val quotrem : int -> int -> int * int **)

  let quotrem a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a

  (** val quot : int -> int -> int **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : int -> int -> int **)

  let rem a b =
    snd (quotrem a b)

  (** val log2 : int -> int **)

  let log2 z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> (Pos.size p))
        (fun p -> (Pos.size p))
        (fun _ -> 0)
        p0)
      (fun _ -> 0)
      z

  (** val sqrt : int -> int **)

  let sqrt n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> (Pos.sqrt p))
      (fun _ -> 0)
      n

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        y)
      x
 end
