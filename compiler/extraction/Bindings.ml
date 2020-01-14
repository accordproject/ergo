open Assoc
open Compat
open CoqLibAdd
open Datatypes
open EquivDec
open List0
open SortingAdd
open String0
open StringAdd

type 'k coq_ODT = { coq_ODT_eqdec : 'k coq_EqDec;
                    coq_ODT_lt_dec : ('k -> 'k -> bool);
                    coq_ODT_compare : ('k -> 'k -> comparison) }

(** val rec_field_lt_dec :
    'a1 coq_ODT -> ('a1 * 'a2) -> ('a1 * 'a2) -> bool **)

let rec_field_lt_dec odt a b =
  let (k, _) = a in let (k0, _) = b in odt.coq_ODT_lt_dec k k0

(** val rec_sort : 'a1 coq_ODT -> ('a1 * 'a2) list -> ('a1 * 'a2) list **)

let rec_sort odt =
  insertion_sort (rec_field_lt_dec odt)

(** val rec_concat_sort :
    'a1 coq_ODT -> ('a1 * 'a2) list -> ('a1 * 'a2) list -> ('a1 * 'a2) list **)

let rec_concat_sort odt l1 l2 =
  rec_sort odt (app l1 l2)

(** val coq_ODT_string : char list coq_ODT **)

let coq_ODT_string =
  { coq_ODT_eqdec = string_eqdec; coq_ODT_lt_dec = StringOrder.lt_dec;
    coq_ODT_compare = StringOrder.compare }

(** val edot : (char list * 'a1) list -> char list -> 'a1 option **)

let edot r a =
  assoc_lookupr coq_ODT_string.coq_ODT_eqdec r a

(** val merge_bindings :
    'a1 coq_EqDec -> (char list * 'a1) list -> (char list * 'a1) list ->
    (char list * 'a1) list option **)

let merge_bindings h l_UU2081_ l_UU2082_ =
  if compatible string_eqdec h l_UU2081_ l_UU2082_
  then Some (rec_concat_sort coq_ODT_string l_UU2081_ l_UU2082_)
  else None

(** val rproject :
    (char list * 'a1) list -> char list list -> (char list * 'a1) list **)

let rproject l s =
  filter (fun x -> if in_dec string_dec (fst x) s then true else false) l

(** val rremove :
    (char list * 'a1) list -> char list -> (char list * 'a1) list **)

let rremove l s =
  filter (fun x -> if string_dec s (fst x) then false else true) l
