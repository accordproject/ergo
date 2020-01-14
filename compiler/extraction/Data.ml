open BinInt
open Bool
open BrandRelation
open CoqLibAdd
open Datatypes
open EquivDec
open FloatAdd
open ForeignData
open String0

type data =
| Coq_dunit
| Coq_dnat of int
| Coq_dfloat of float
| Coq_dbool of bool
| Coq_dstring of char list
| Coq_dcoll of data list
| Coq_drec of (char list * data) list
| Coq_dleft of data
| Coq_dright of data
| Coq_dbrand of brands * data
| Coq_dforeign of foreign_data_model

(** val data_eq_dec : foreign_data -> data -> data -> bool **)

let rec data_eq_dec fdata x y =
  match x with
  | Coq_dunit -> (match y with
                  | Coq_dunit -> true
                  | _ -> false)
  | Coq_dnat x0 -> (match y with
                    | Coq_dnat z -> Z.eq_dec x0 z
                    | _ -> false)
  | Coq_dfloat x0 ->
    (match y with
     | Coq_dfloat f0 -> float_eq_dec x0 f0
     | _ -> false)
  | Coq_dbool x0 -> (match y with
                     | Coq_dbool b0 -> bool_dec x0 b0
                     | _ -> false)
  | Coq_dstring x0 ->
    (match y with
     | Coq_dstring s0 -> string_dec x0 s0
     | _ -> false)
  | Coq_dcoll x0 ->
    (match y with
     | Coq_dcoll l ->
       list_Forallt_eq_dec x0 l
         (let rec f2 = function
          | [] -> Forallt_nil
          | d :: c0 -> Forallt_cons (d, c0, (data_eq_dec fdata d), (f2 c0))
          in f2 x0)
     | _ -> false)
  | Coq_drec x0 ->
    (match y with
     | Coq_drec l ->
       list_Forallt_eq_dec x0 l
         (forallt_impl x0
           (let rec f3 = function
            | [] -> Forallt_nil
            | sd :: c0 ->
              Forallt_cons (sd, c0, (data_eq_dec fdata (snd sd)), (f3 c0))
            in f3 x0)
           (forallt_weaken (fun x1 h y0 ->
             let (s, d) = x1 in
             let (s0, d0) = y0 in
             pair_eq_dec s d s0 d0 (string_dec s s0) (h d0)) x0))
     | _ -> false)
  | Coq_dleft x0 ->
    (match y with
     | Coq_dleft y0 -> data_eq_dec fdata x0 y0
     | _ -> false)
  | Coq_dright x0 ->
    (match y with
     | Coq_dright y0 -> data_eq_dec fdata x0 y0
     | _ -> false)
  | Coq_dbrand (b, x0) ->
    (match y with
     | Coq_dbrand (b0, y0) ->
       let s = equiv_dec (list_eqdec string_eqdec) b b0 in
       if s then data_eq_dec fdata x0 y0 else false
     | _ -> false)
  | Coq_dforeign fd ->
    (match y with
     | Coq_dforeign f -> fdata.foreign_data_dec fd f
     | _ -> false)

(** val data_eqdec : foreign_data -> data coq_EqDec **)

let data_eqdec =
  data_eq_dec

(** val dsome : foreign_data -> data -> data **)

let dsome _ x =
  Coq_dleft x

(** val dnone : foreign_data -> data **)

let dnone _ =
  Coq_dright Coq_dunit
