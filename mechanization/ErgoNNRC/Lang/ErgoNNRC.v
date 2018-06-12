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
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoNNRC.

  Section Syntax.

    (** Expression *)
    Definition nnrc_expr := ErgoCodeGen.nnrc_expr.

    Record lambdan :=
      mkLambdaN
        { lambdan_params: list (string * cto_type);
          lambdan_output : cto_type;
          lambdan_throws : option cto_type;
          lambdan_emits : option cto_type;
          lambdan_body : nnrc_expr; }.

    (** Clause *)
    Record nnrc_clause :=
      mkClauseN
        { clausen_name : string;
          clausen_lambda : lambdan; }.

    (** Function *)
    Record nnrc_function :=
      mkFuncN
        { functionn_name : string;
          functionn_lambda : lambdan; }.

    (** Contract *)
    Record nnrc_contract :=
      mkContractN
        { contractn_name : string;
          contractn_template : string;
          contractn_clauses : list nnrc_clause; }.

    (** Declaration *)
    Inductive nnrc_declaration :=
    | ENExpr : nnrc_expr -> nnrc_declaration
    | ENGlobal : string -> nnrc_expr -> nnrc_declaration
    | ENFunc : nnrc_function -> nnrc_declaration
    | ENContract : nnrc_contract -> nnrc_declaration.
    
    (** Package. *)
    Record nnrc_package :=
      mkPackageN
        { packagen_namespace : string;
          packagen_declarations : list nnrc_declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End ErgoNNRC.

