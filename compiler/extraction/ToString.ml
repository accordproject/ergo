open CoqLibAdd
open Digits

(** val boolToString : bool -> char list **)

let boolToString = function
| true -> 't'::('r'::('u'::('e'::[])))
| false -> 'f'::('a'::('l'::('s'::('e'::[]))))

(** val stringToString : char list -> char list **)

let stringToString s =
  s

(** val coq_ToString_Z : int coq_ToString **)

let coq_ToString_Z =
  coq_Z_to_string10

(** val coq_ToString_float : float coq_ToString **)

let coq_ToString_float =
  (fun x -> Util.char_list_of_string (Util.qcert_string_of_float x))

(** val coq_ToString_bool : bool coq_ToString **)

let coq_ToString_bool =
  boolToString
