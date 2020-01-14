open Datatypes
open List0
open NativeString

(** val nstring_multi_append :
    nstring -> ('a1 -> nstring) -> 'a1 list -> nstring **)

let nstring_multi_append separator f = function
| [] -> nstring_quote []
| e :: elems' ->
  fold_left (fun acc e0 ->
    nstring_append acc (nstring_append separator (f e0))) elems' (f e)

(** val get_local_part : char list -> char list option **)

let get_local_part = (fun name -> Util.get_local_part name)

(** val find_duplicate : char list list -> char list option **)

let find_duplicate = (fun l -> Util.find_duplicate l)

(** val filter_some : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec filter_some f = function
| [] -> []
| x :: t ->
  (match f x with
   | Some x' -> x' :: (filter_some f t)
   | None -> filter_some f t)

(** val postpend : 'a1 list -> 'a1 -> 'a1 list **)

let postpend ls a =
  app ls (a :: [])

(** val last_some_pair :
    ('a1 option * 'a2 option) list -> 'a1 option * 'a2 option **)

let last_some_pair l =
  let proc_one = fun one acc ->
    let (o, o0) = acc in
    (match o with
     | Some _ -> (match o0 with
                  | Some _ -> acc
                  | None -> one)
     | None -> one)
  in
  fold_right proc_one (None, None) l

(** val coq_coq_distinct : ('a1 -> char list) -> 'a1 list -> 'a1 list **)

let coq_coq_distinct = (fun name l -> Util.coq_distinct name l)

(** val coq_coq_toposort :
    ('a1 -> 'a2) -> ('a1 -> char list) -> ('a1 * 'a1 list) list -> 'a1 list **)

let coq_coq_toposort = (fun label file g -> Util.coq_toposort label file g)

(** val coq_coq_sort_given_topo_order :
    'a1 list -> ('a1 -> char list) -> ('a2 -> char list) -> ('a1 ->
    char list) -> 'a2 list -> 'a2 list **)

let coq_coq_sort_given_topo_order = (fun labely labelx file order l -> Util.coq_sort_given_topo_order labely labelx file order l)

(** val coq_coq_time : char list -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let coq_coq_time = (fun msg f x -> Util.coq_time msg f x)
