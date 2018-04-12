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

(** Ergo is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculus.

  Section Syntax.

    (** Expression *)
    Definition ergoc_expr := ErgoCodeGen.ergoc_expr.

    (** Clause *)
    Definition ergoc_clause := @clause ergoc_expr.
    
    (** Function *)
    Definition ergoc_func := @func ergoc_expr.
    
    (** Declaration *)
    Definition ergoc_declaration := @declaration ergoc_expr.
    
    (** Contract *)
    Definition ergoc_contract := @contract ergoc_expr.
    
    (** Statement *)
    Definition ergoc_stmt := @stmt ergoc_expr.

    (** Package. *)
    Definition ergoc_package := @package ergoc_expr.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End ErgoCalculus.

