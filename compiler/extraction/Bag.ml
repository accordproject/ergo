open BinInt
open Datatypes
open EquivDec
open List0

(** val bunion : 'a1 list -> 'a1 list -> 'a1 list **)

let bunion =
  app

(** val remove_one : 'a1 coq_EqDec -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove_one eqdec x = function
| [] -> []
| y :: tl -> if equiv_dec eqdec x y then tl else y :: (remove_one eqdec x tl)

(** val bminus : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec bminus eqdec d x =
  match d with
  | [] -> x
  | d1 :: d' -> bminus eqdec d' (remove_one eqdec d1 x)

(** val mult : 'a1 coq_EqDec -> 'a1 list -> 'a1 -> int **)

let rec mult eqdec l a =
  match l with
  | [] -> 0
  | b :: l' ->
    if equiv_dec eqdec a b
    then Pervasives.succ (mult eqdec l' a)
    else mult eqdec l' a

(** val bmin : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list **)

let bmin eqdec l1 l2 =
  bminus eqdec (bminus eqdec l2 l1) l1

(** val bmax : 'a1 coq_EqDec -> 'a1 list -> 'a1 list -> 'a1 list **)

let bmax eqdec l1 l2 =
  bunion l1 (bminus eqdec l1 l2)

(** val bcount : 'a1 list -> int **)

let bcount =
  length

(** val bdistinct : 'a1 coq_EqDec -> 'a1 list -> 'a1 list **)

let rec bdistinct eqdec = function
| [] -> []
| x :: l' ->
  let dl' = bdistinct eqdec l' in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> x :: dl')
     (fun _ -> dl')
     (mult eqdec dl' x))

(** val bnummin : int list -> int **)

let bnummin = function
| [] -> 0
| x0 :: l' -> fold_right Z.min x0 l'

(** val bnummax : int list -> int **)

let bnummax = function
| [] -> 0
| x0 :: l' -> fold_right Z.max x0 l'
