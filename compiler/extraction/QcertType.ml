open EquivDec
open ForeignType
open Lattice

type enhanced_type =
| Coq_enhancedTop
| Coq_enhancedBottom
| Coq_enhancedString
| Coq_enhancedDateTimeFormat
| Coq_enhancedDateTime
| Coq_enhancedDateTimeDuration
| Coq_enhancedDateTimePeriod

(** val enhanced_type_join :
    enhanced_type -> enhanced_type -> enhanced_type **)

let enhanced_type_join t1 t2 =
  match t1 with
  | Coq_enhancedTop ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | _ -> Coq_enhancedTop)
  | Coq_enhancedBottom -> t2
  | Coq_enhancedString ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | Coq_enhancedString -> Coq_enhancedString
     | _ -> Coq_enhancedTop)
  | Coq_enhancedDateTimeFormat ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | Coq_enhancedDateTimeFormat -> Coq_enhancedDateTimeFormat
     | _ -> Coq_enhancedTop)
  | Coq_enhancedDateTime ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | Coq_enhancedDateTime -> Coq_enhancedDateTime
     | _ -> Coq_enhancedTop)
  | Coq_enhancedDateTimeDuration ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | Coq_enhancedDateTimeDuration -> Coq_enhancedDateTimeDuration
     | _ -> Coq_enhancedTop)
  | Coq_enhancedDateTimePeriod ->
    (match t2 with
     | Coq_enhancedBottom -> t1
     | Coq_enhancedDateTimePeriod -> Coq_enhancedDateTimePeriod
     | _ -> Coq_enhancedTop)

(** val enhanced_type_meet :
    enhanced_type -> enhanced_type -> enhanced_type **)

let enhanced_type_meet t1 t2 =
  match t1 with
  | Coq_enhancedTop -> t2
  | Coq_enhancedBottom ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | _ -> Coq_enhancedBottom)
  | Coq_enhancedString ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | Coq_enhancedString -> Coq_enhancedString
     | _ -> Coq_enhancedBottom)
  | Coq_enhancedDateTimeFormat ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | Coq_enhancedDateTimeFormat -> Coq_enhancedDateTimeFormat
     | _ -> Coq_enhancedBottom)
  | Coq_enhancedDateTime ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | Coq_enhancedDateTime -> Coq_enhancedDateTime
     | _ -> Coq_enhancedBottom)
  | Coq_enhancedDateTimeDuration ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | Coq_enhancedDateTimeDuration -> Coq_enhancedDateTimeDuration
     | _ -> Coq_enhancedBottom)
  | Coq_enhancedDateTimePeriod ->
    (match t2 with
     | Coq_enhancedTop -> t1
     | Coq_enhancedDateTimePeriod -> Coq_enhancedDateTimePeriod
     | _ -> Coq_enhancedBottom)

(** val enhanced_type_lattice : enhanced_type coq_Lattice **)

let enhanced_type_lattice =
  { meet = enhanced_type_meet; join = enhanced_type_join }

(** val enhanced_foreign_type_obligation_1 : enhanced_type coq_EqDec **)

let enhanced_foreign_type_obligation_1 x y =
  match x with
  | Coq_enhancedTop -> (match y with
                        | Coq_enhancedTop -> true
                        | _ -> false)
  | Coq_enhancedBottom ->
    (match y with
     | Coq_enhancedBottom -> true
     | _ -> false)
  | Coq_enhancedString ->
    (match y with
     | Coq_enhancedString -> true
     | _ -> false)
  | Coq_enhancedDateTimeFormat ->
    (match y with
     | Coq_enhancedDateTimeFormat -> true
     | _ -> false)
  | Coq_enhancedDateTime ->
    (match y with
     | Coq_enhancedDateTime -> true
     | _ -> false)
  | Coq_enhancedDateTimeDuration ->
    (match y with
     | Coq_enhancedDateTimeDuration -> true
     | _ -> false)
  | Coq_enhancedDateTimePeriod ->
    (match y with
     | Coq_enhancedDateTimePeriod -> true
     | _ -> false)

(** val enhanced_foreign_type_obligation_2 :
    enhanced_type -> enhanced_type -> bool **)

let enhanced_foreign_type_obligation_2 a b =
  match a with
  | Coq_enhancedTop -> (match b with
                        | Coq_enhancedTop -> true
                        | _ -> false)
  | Coq_enhancedBottom -> true
  | Coq_enhancedString ->
    (match b with
     | Coq_enhancedTop -> true
     | Coq_enhancedString -> true
     | _ -> false)
  | Coq_enhancedDateTimeFormat ->
    (match b with
     | Coq_enhancedTop -> true
     | Coq_enhancedDateTimeFormat -> true
     | _ -> false)
  | Coq_enhancedDateTime ->
    (match b with
     | Coq_enhancedTop -> true
     | Coq_enhancedDateTime -> true
     | _ -> false)
  | Coq_enhancedDateTimeDuration ->
    (match b with
     | Coq_enhancedTop -> true
     | Coq_enhancedDateTimeDuration -> true
     | _ -> false)
  | Coq_enhancedDateTimePeriod ->
    (match b with
     | Coq_enhancedTop -> true
     | Coq_enhancedDateTimePeriod -> true
     | _ -> false)

(** val enhanced_foreign_type : foreign_type **)

let enhanced_foreign_type =
  { foreign_type_dec = (Obj.magic enhanced_foreign_type_obligation_1);
    foreign_type_lattice = (Obj.magic enhanced_type_lattice);
    foreign_type_sub_dec = (fun a b ->
    enhanced_foreign_type_obligation_2 (Obj.magic a) (Obj.magic b)) }
