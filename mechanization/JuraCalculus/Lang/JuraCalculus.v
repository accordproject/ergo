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

(** Jura is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import Qcert.Common.CommonRuntime.
Require Import Qcert.NNRC.NNRCRuntime.
Require Import JuraBase.

Section JuraCalculus.
  Context {fruntime:foreign_runtime}.
  
  Section Syntax.

    (** Expression *)
    Definition jurac_expr := nnrc.

    (** Clause *)
    Definition jurac_clause := @clause jurac_expr.
    
    (** Function *)
    Definition jurac_func := @func jurac_expr.
    
    (** Declaration *)
    Definition jurac_declaration := @declaration jurac_expr.
    
    (** Contract *)
    Definition jurac_contract := @contract jurac_expr.
    
    (** Statement *)
    Definition jurac_stmt := @stmt jurac_expr.

    (** Package. *)
    Definition jurac_package := @package jurac_expr.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- denotational semantics should go here *)
  End Semantics.
End JuraCalculus.

