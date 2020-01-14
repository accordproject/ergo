open EquivDec

(** val lift : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let lift f = function
| Some a' -> Some (f a')
| None -> None

(** val olift : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let olift f = function
| Some x' -> f x'
| None -> None

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind a b =
  olift b a

(** val lift2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option **)

let lift2 f x y =
  match x with
  | Some x' -> (match y with
                | Some y' -> Some (f x' y')
                | None -> None)
  | None -> None

(** val mk_lazy_lift :
    'a1 coq_EqDec -> ('a2 -> 'a1 -> 'a1 -> 'a2) -> 'a2 -> 'a1 -> 'a1 -> 'a2 **)

let mk_lazy_lift dec f b a1 a2 =
  if equiv_dec dec a1 a2 then b else f b a1 a2
