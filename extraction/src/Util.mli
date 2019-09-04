(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(* This module contains a few basic utilities *)

(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

val string_of_char_list : char list -> string
val char_list_of_string : string -> char list
val char_list_append : char list -> char list -> char list
val coq_Z_of_int : int -> int

(*******)
(* I/O *)
(*******)

val os_newline : string
val string_of_file : string -> string

(* File print *)

val make_file : string -> string -> unit

(* Make up target file name *)

val target_f : string option -> string -> string
val outname : string -> string -> string


(**********************************)
(* Support for Enhanced operators *)
(**********************************)

val float_sum : float list -> float
val float_arithmean : float list -> float
val float_listmin : float list -> float
val float_listmax : float list -> float

val string_of_enhanced_float : float -> char list
val string_of_enhanced_string : string -> char list
val qcert_string_of_float : float -> string
val ergo_float_of_string : char list -> float option

(* Timing function for CompStat   *)

val time : ('a -> 'b) -> 'a -> char list * 'b


(* String Manipulation *)

val global_replace : string -> string -> string -> string
(** [global_replace const templ s] returns a string identical to [s],
    except thta all substrings of [s] that match the string [const] have
    been replaced by [templ]. This is intended as a replacement for the
    corresponding function in Str when matching against a constant
    string. *)

val filename_append : string -> string list -> string
(** [filename_append dir subdirlist] Append sub-directories to a root directory *)

val loc_error : string -> ('a -> 'b) -> 'a -> 'b

val map_assoc : ('a -> 'b -> 'c) -> (('a * 'b) list) -> 'c list

(* Mini topo-sort *)
(* XXX To be revised when Coq-level DFS-topological sort is complete *)

exception TopoCycle of string list
val toposort : ('a -> 'b) -> ('a -> string) -> ('a * 'a list) list -> 'a list
val coq_distinct : ('a -> char list) -> 'a list -> 'a list
val coq_toposort : ('a -> 'b) -> ('a -> char list) -> ('a * 'a list) list -> 'a list
val coq_sort_given_topo_order : 'a list -> ('a -> char list) -> ('c -> char list) -> ('a -> char list) -> 'c list -> 'c list

val get_local_part : char list -> (char list) option

val class_prefix_of_filename : string -> string

type nrc_logger_token_type = string

(** Monitoring *)
val coq_time : char list -> ('a -> 'b) -> 'a -> 'b
val monitoring : bool ref
val get_monitor_output : unit -> string

val flat_map_string : (char -> string) -> string -> string

val find_duplicate : char list list -> char list option

val coq_print_warnings : char list -> char list list -> 'a -> 'a

(* Encoding/Decoding *)
val encode_string : char list -> char list
val decode_string : char list -> char list


