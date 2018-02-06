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

(* This module contains parsing utilities *)

open SExp
open JComp
open JuraCompiler

val sexp_to_data : sexp -> Data.qdata
val data_to_sexp : Data.qdata -> sexp

val sexp_to_nnrc : sexp -> nnrc
val nnrc_to_sexp : nnrc -> sexp

val sexp_to_jurac_package : sexp -> jurac_package
val jurac_package_to_sexp : jurac_package -> sexp

