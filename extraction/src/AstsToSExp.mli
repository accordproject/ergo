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
open ErgoComp
open ErgoCompiler

val sexp_to_data : sexp -> ErgoData.data
val data_to_sexp : ErgoData.data -> sexp

val sexp_to_nnrc : sexp -> nnrc
val nnrc_to_sexp : nnrc -> sexp

val sexp_to_ergoc_package : sexp -> ergoc_package
val ergoc_package_to_sexp : ergoc_package -> sexp

