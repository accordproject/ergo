open Bag
open BinInt
open Data
open DataLift
open Datatypes
open FloatAdd
open ForeignData
open Lift
open LiftIterators
open String0

(** val dsum : foreign_data -> data list -> int option **)

let rec dsum fdata = function
| [] -> Some 0
| d :: ls ->
  (match d with
   | Coq_dnat n -> lift (Z.add n) (dsum fdata ls)
   | _ -> None)

(** val darithmean : foreign_data -> data list -> int option **)

let darithmean fdata ns =
  lift (fun x -> Z.quot x (Z.of_nat (Datatypes.length ns))) (dsum fdata ns)

(** val lifted_stringbag :
    foreign_data -> data list -> char list list option **)

let lifted_stringbag fdata l =
  lift_map (ondstring fdata (fun x -> x)) l

(** val lifted_zbag : foreign_data -> data list -> int list option **)

let lifted_zbag fdata l =
  lift_map (ondnat fdata (fun x -> x)) l

(** val lifted_min : foreign_data -> data list -> data option **)

let lifted_min fdata l =
  lift (fun x -> Coq_dnat x) (lift bnummin (lifted_zbag fdata l))

(** val lifted_max : foreign_data -> data list -> data option **)

let lifted_max fdata l =
  lift (fun x -> Coq_dnat x) (lift bnummax (lifted_zbag fdata l))

(** val lifted_fbag : foreign_data -> data list -> float list option **)

let lifted_fbag fdata l =
  lift_map (ondfloat fdata (fun x -> x)) l

(** val lifted_fsum : foreign_data -> data list -> data option **)

let lifted_fsum fdata l =
  lift (fun x -> Coq_dfloat x) (lift float_list_sum (lifted_fbag fdata l))

(** val lifted_farithmean : foreign_data -> data list -> data option **)

let lifted_farithmean fdata l =
  lift (fun x -> Coq_dfloat x)
    (lift float_list_arithmean (lifted_fbag fdata l))

(** val lifted_fmin : foreign_data -> data list -> data option **)

let lifted_fmin fdata l =
  lift (fun x -> Coq_dfloat x) (lift float_list_min (lifted_fbag fdata l))

(** val lifted_fmax : foreign_data -> data list -> data option **)

let lifted_fmax fdata l =
  lift (fun x -> Coq_dfloat x) (lift float_list_max (lifted_fbag fdata l))

(** val lifted_join :
    foreign_data -> char list -> data list -> data option **)

let lifted_join fdata sep l =
  lift (fun x -> Coq_dstring x) (lift (concat sep) (lifted_stringbag fdata l))
