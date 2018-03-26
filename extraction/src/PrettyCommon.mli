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

open JComp
open JuraCompiler

(* Useful for SExp support *)
val timescale_as_string : time_scale -> string

val string_of_foreign_data : enhanced_data -> string
val foreign_data_of_string : string -> enhanced_data

val string_of_foreign_unary_op : enhanced_unary_op -> string
val string_of_nat_arith_unary_op : nat_arith_unary_op -> string
val string_of_float_arith_unary_op : float_arith_unary_op -> string

val foreign_unary_op_of_string : string -> enhanced_unary_op
val nat_arith_unary_op_of_string : string -> nat_arith_unary_op
val float_arith_unary_op_of_string : string -> float_arith_unary_op

val string_of_foreign_binary_op : enhanced_binary_op -> string
val string_of_nat_arith_binary_op : nat_arith_binary_op -> string
val string_of_float_arith_binary_op : float_arith_binary_op -> string
val string_of_float_compare_binary_op : float_compare_binary_op -> string

val nat_arith_binary_op_of_string : string -> nat_arith_binary_op
val float_arith_binary_op_of_string : string -> float_arith_binary_op
val foreign_binary_op_of_string : string -> enhanced_binary_op
val float_compare_binary_op_of_string : string -> float_compare_binary_op

val string_of_binary_op : binary_op -> string

