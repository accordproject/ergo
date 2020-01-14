open Data
open Datatypes
open EJson
open Encode
open ForeignDataToEJson
open ForeignEJson
open ForeignRuntime
open List0
open SortingDesc

(** val data_to_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    data -> 'a1 ejson **)

let rec data_to_ejson fruntime fejson fdatatoejson = function
| Coq_dunit -> Coq_ejnull
| Coq_dnat n -> Coq_ejbigint n
| Coq_dfloat n -> Coq_ejnumber n
| Coq_dbool b -> Coq_ejbool b
| Coq_dstring s -> Coq_ejstring s
| Coq_dcoll c ->
  Coq_ejarray (map (data_to_ejson fruntime fejson fdatatoejson) c)
| Coq_drec r ->
  Coq_ejobject
    (map (fun x -> ((key_encode (fst x)),
      (data_to_ejson fruntime fejson fdatatoejson (snd x)))) r)
| Coq_dleft d' ->
  Coq_ejobject ((('$'::('l'::('e'::('f'::('t'::[]))))),
    (data_to_ejson fruntime fejson fdatatoejson d')) :: [])
| Coq_dright d' ->
  Coq_ejobject ((('$'::('r'::('i'::('g'::('h'::('t'::[])))))),
    (data_to_ejson fruntime fejson fdatatoejson d')) :: [])
| Coq_dbrand (b, d') ->
  Coq_ejobject ((('$'::('c'::('l'::('a'::('s'::('s'::[])))))), (Coq_ejarray
    (map (fun x -> Coq_ejstring x) b))) :: ((('$'::('d'::('a'::('t'::('a'::[]))))),
    (data_to_ejson fruntime fejson fdatatoejson d')) :: []))
| Coq_dforeign fd ->
  Coq_ejforeign (fdatatoejson.foreign_to_ejson_from_data fd)

(** val sortCriteria_to_ejson : (char list * coq_SortDesc) -> 'a1 ejson **)

let sortCriteria_to_ejson = function
| (lbl, c) ->
  (match c with
   | Descending ->
     Coq_ejobject ((('d'::('e'::('s'::('c'::[])))), (Coq_ejstring
       (key_encode lbl))) :: [])
   | Ascending ->
     Coq_ejobject ((('a'::('s'::('c'::[]))), (Coq_ejstring
       (key_encode lbl))) :: []))
