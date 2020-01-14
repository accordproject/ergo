open List0

type nstring = string

(** val nstring_quote : char list -> nstring **)

let nstring_quote = (fun s1 -> Util.string_of_char_list s1)

(** val nstring_append : nstring -> nstring -> nstring **)

let nstring_append = (fun s1 s2 -> s1 ^ s2)

(** val nstring_flat_map : (char -> nstring) -> nstring -> nstring **)

let nstring_flat_map = (fun f s -> Util.flat_map_string f s)

(** val nstring_concat : nstring -> nstring list -> nstring **)

let rec nstring_concat sep = function
| [] -> nstring_quote []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> nstring_append (nstring_append x sep) (nstring_concat sep xs))

(** val nstring_map_concat :
    nstring -> ('a1 -> nstring) -> 'a1 list -> nstring **)

let nstring_map_concat separator f = function
| [] -> nstring_quote []
| e :: elems' ->
  fold_left (fun acc e0 ->
    nstring_append (nstring_append acc separator) (f e0)) elems' (f e)
