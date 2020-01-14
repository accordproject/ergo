open Datatypes

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

(** val divmod : int -> int -> int -> int -> int * int **)

let rec divmod x y q u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (q, u))
    (fun x' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> divmod x' y (Pervasives.succ q) y)
      (fun u' -> divmod x' y q u')
      u)
    x

(** val div : int -> int -> int **)

let div x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> y)
    (fun y' -> fst (divmod x y' 0 y'))
    y

(** val modulo : int -> int -> int **)

let modulo x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> y)
    (fun y' -> sub y' (snd (divmod x y' 0 y')))
    y
