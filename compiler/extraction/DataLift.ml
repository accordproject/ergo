open Data
open ForeignData
open Lift

(** val unbdbool :
    foreign_data -> (bool -> bool -> bool) -> data -> data -> data option **)

let unbdbool _ f d1 d2 =
  match d1 with
  | Coq_dbool b1 ->
    (match d2 with
     | Coq_dbool b2 -> Some (Coq_dbool (f b1 b2))
     | _ -> None)
  | _ -> None

(** val unudbool : foreign_data -> (bool -> bool) -> data -> data option **)

let unudbool _ f = function
| Coq_dbool b -> Some (Coq_dbool (f b))
| _ -> None

(** val unbdnat :
    foreign_data -> (int -> int -> bool) -> data -> data -> data option **)

let unbdnat _ f d1 d2 =
  match d1 with
  | Coq_dnat n1 ->
    (match d2 with
     | Coq_dnat n2 -> Some (Coq_dbool (f n1 n2))
     | _ -> None)
  | _ -> None

(** val unbdata :
    foreign_data -> (data -> data -> bool) -> data -> data -> data option **)

let unbdata _ f d1 d2 =
  Some (Coq_dbool (f d1 d2))

(** val unndstring :
    foreign_data -> (char list -> int) -> data -> data option **)

let unndstring _ f = function
| Coq_dstring s1 -> Some (Coq_dnat (f s1))
| _ -> None

(** val unsdstring :
    foreign_data -> (char list -> char list -> char list) -> data -> data ->
    data option **)

let unsdstring _ f d1 d2 =
  match d1 with
  | Coq_dstring s1 ->
    (match d2 with
     | Coq_dstring s2 -> Some (Coq_dstring (f s1 s2))
     | _ -> None)
  | _ -> None

(** val ondcoll2 :
    foreign_data -> (data list -> data list -> 'a1) -> data -> data -> 'a1
    option **)

let ondcoll2 _ f d1 d2 =
  match d1 with
  | Coq_dcoll l -> (match d2 with
                    | Coq_dcoll l0 -> Some (f l l0)
                    | _ -> None)
  | _ -> None

(** val rondcoll2 :
    foreign_data -> (data list -> data list -> data list) -> data -> data ->
    data option **)

let rondcoll2 fdata f d1 d2 =
  lift (fun x -> Coq_dcoll x) (ondcoll2 fdata f d1 d2)

(** val ondstring :
    foreign_data -> (char list -> 'a1) -> data -> 'a1 option **)

let ondstring _ f = function
| Coq_dstring n -> Some (f n)
| _ -> None

(** val ondnat : foreign_data -> (int -> 'a1) -> data -> 'a1 option **)

let ondnat _ f = function
| Coq_dnat n -> Some (f n)
| _ -> None

(** val ondfloat : foreign_data -> (float -> 'a1) -> data -> 'a1 option **)

let ondfloat _ f = function
| Coq_dfloat n -> Some (f n)
| _ -> None

(** val ondcoll : foreign_data -> (data list -> 'a1) -> data -> 'a1 option **)

let ondcoll _ f = function
| Coq_dcoll l -> Some (f l)
| _ -> None

(** val lift_oncoll :
    foreign_data -> (data list -> 'a1 option) -> data -> 'a1 option **)

let lift_oncoll _ f = function
| Coq_dcoll l -> f l
| _ -> None

(** val rondcoll :
    foreign_data -> (data list -> data list) -> data -> data option **)

let rondcoll fdata f d =
  lift (fun x -> Coq_dcoll x) (ondcoll fdata f d)
