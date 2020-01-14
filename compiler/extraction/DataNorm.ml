open Bindings
open BrandRelation
open Data
open Datatypes
open ForeignData
open List0

(** val normalize_data : foreign_data -> brand_relation_t -> data -> data **)

let rec normalize_data fdata h d = match d with
| Coq_dcoll l -> Coq_dcoll (map (normalize_data fdata h) l)
| Coq_drec rl ->
  Coq_drec
    (rec_sort coq_ODT_string
      (map (fun x -> ((fst x), (normalize_data fdata h (snd x)))) rl))
| Coq_dleft l -> Coq_dleft (normalize_data fdata h l)
| Coq_dright l -> Coq_dright (normalize_data fdata h l)
| Coq_dbrand (b, d0) ->
  Coq_dbrand ((canon_brands h b), (normalize_data fdata h d0))
| Coq_dforeign fd -> Coq_dforeign (fdata.foreign_data_normalize fd)
| _ -> d
