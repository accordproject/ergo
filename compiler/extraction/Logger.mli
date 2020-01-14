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

(* This module contains the implementation for the optimization logger *)

open Util
open SExp

val nrc_log_startPass : string -> 'a -> nrc_logger_token_type
val nrc_log_step : nrc_logger_token_type -> string -> 'a -> 'a -> nrc_logger_token_type
val nrc_log_endPass : nrc_logger_token_type -> 'a -> nrc_logger_token_type

val nrc_set_trace : (Obj.t->sexp) -> string -> unit

val log_string : char list -> unit

