open CoqLibAdd
open Datatypes
open Digits
open EquivDec
open List0
open Nat
open String0
open StringAdd

(** val find_bounded :
    ('a1 -> 'a1) -> ('a1 -> bool) -> int -> 'a1 -> 'a1 option **)

let rec find_bounded incr f bound init =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n ->
    if f init then Some init else find_bounded incr f n (incr init))
    bound

(** val find_bounded_S_nin_finds :
    (int -> 'a1) -> 'a1 coq_EqDec -> 'a1 list -> int -> 'a1 **)

let find_bounded_S_nin_finds f dec dom bound =
  match find_bounded (fun x -> Pervasives.succ x) (fun x ->
          if in_dec (equiv_dec dec) (f x) dom then false else true) bound 0 with
  | Some n -> f n
  | None -> assert false (* absurd case *)

(** val find_fresh_inj_f :
    'a1 coq_EqDec -> (int -> 'a1) -> 'a1 list -> 'a1 **)

let find_fresh_inj_f dec f dom =
  find_bounded_S_nin_finds f dec dom (Pervasives.succ (Datatypes.length dom))

(** val find_fresh_string : char list list -> char list **)

let find_fresh_string dom =
  find_fresh_inj_f string_eqdec nat_to_string16 dom

(** val fresh_var : char list -> char list list -> char list **)

let fresh_var pre dom =
  let problems = filter (prefix pre) dom in
  let problemEnds =
    map (fun x -> substring (length pre) (sub (length x) (length pre)) x)
      problems
  in
  append pre (find_fresh_string problemEnds)

(** val fresh_var2 :
    char list -> char list -> char list list -> char list * char list **)

let fresh_var2 pre1 pre2 dom =
  let fresh_var1 = fresh_var pre1 dom in
  (fresh_var1, (fresh_var pre2 (fresh_var1 :: dom)))

(** val get_var_base : char list -> char list -> char list **)

let get_var_base sep var =
  match index 0 (string_reverse sep) (string_reverse var) with
  | Some n -> substring 0 (sub (length var) (Pervasives.succ n)) var
  | None -> var

(** val fresh_var_from :
    char list -> char list -> char list list -> char list **)

let fresh_var_from sep oldvar dom =
  if in_dec string_dec oldvar dom
  then fresh_var (append (get_var_base sep oldvar) sep) dom
  else oldvar
