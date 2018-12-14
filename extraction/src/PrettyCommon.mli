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

(** This module contains common code for pretty-printers *)

open ErgoComp

(* Character sets *)

type charkind =
  | Ascii
  | Greek

type pretty_config

val default_pretty_config : unit -> pretty_config

val set_ascii : pretty_config -> unit -> unit
val set_greek : pretty_config -> unit -> unit
val get_charset : pretty_config -> charkind
val get_charset_bool : pretty_config -> bool

val set_type_annotations : pretty_config -> unit -> unit
val set_no_type_annotations : pretty_config -> unit -> unit
val get_type_annotations : pretty_config -> bool

val set_margin : pretty_config -> int -> unit
val get_margin : pretty_config -> int

val set_inheritance : pretty_config -> json -> unit
val get_inheritance : pretty_config -> json

val set_link_js_runtime : pretty_config -> unit -> unit
val link_js_runtime : pretty_config -> bool

(* Pretty sym *)

type symbols =
    { chi: (string*int);
      chiflat: (string*int);
      chie: (string*int);
      join: (string*int);
      djoin: (string*int);
      times: (string*int);
      sigma: (string*int);
      langle: (string*int);
      rangle: (string*int);
      llangle: (string*int);
      rrangle: (string*int);
      lpangle: (string*int);
      rpangle: (string*int);
      bars: (string*int);
      lrarrow: (string*int);
      sqlrarrow: (string*int);
      lfloor: (string*int);
      rfloor: (string*int);
      circ: (string*int);
      circe: (string*int);
      sharp: (string*int);
      pi: (string*int);
      bpi: (string*int);
      gamma: (string*int);
      rho: (string*int);
      cup: (string*int);
      vee: (string*int);
      wedge: (string*int);
      leq: (string*int);
      sin: (string*int);
      neg: (string*int);
      top: (string*int);
      bot: (string*int) }

val greeksym : symbols
val textsym : symbols
val pretty_sym : Format.formatter -> (string*int) -> unit

(* Pretty utils *)

type 'a pretty_fun = int -> symbols -> Format.formatter -> 'a -> unit
val pretty_infix_exp : int -> int -> symbols -> 'a pretty_fun -> (string*int) -> Format.formatter -> 'a -> 'a -> unit
val pretty_squared_names : symbols -> Format.formatter -> (char list) list -> unit

(* Pretty data *)

val pretty_data : Format.formatter -> data -> unit

(* Pretty qcert_type *)

val pretty_rtype_aux : symbols -> Format.formatter -> ErgoCTypes.ectype_struct -> unit

(* Pretty operators *)

val pretty_unary_op : int -> symbols -> 'a pretty_fun -> Format.formatter -> unary_op -> 'a -> unit
val pretty_binary_op : int -> symbols -> 'a pretty_fun -> Format.formatter -> binary_op -> 'a -> 'a -> unit

(* Useful for SExp support *)

val string_of_foreign_data : enhanced_data -> string

val string_of_foreign_unary_op : enhanced_unary_op -> string
val string_of_nat_arith_unary_op : nat_arith_unary_op -> string
val string_of_float_arith_unary_op : float_arith_unary_op -> string

val nat_arith_unary_op_of_string : string -> nat_arith_unary_op
val float_arith_unary_op_of_string : string -> float_arith_unary_op

val string_of_foreign_binary_op : enhanced_binary_op -> string
val string_of_nat_arith_binary_op : nat_arith_binary_op -> string
val string_of_float_arith_binary_op : float_arith_binary_op -> string
val string_of_float_compare_binary_op : float_compare_binary_op -> string

val nat_arith_binary_op_of_string : string -> nat_arith_binary_op
val float_arith_binary_op_of_string : string -> float_arith_binary_op
val float_compare_binary_op_of_string : string -> float_compare_binary_op

val string_of_binary_op : binary_op -> string

