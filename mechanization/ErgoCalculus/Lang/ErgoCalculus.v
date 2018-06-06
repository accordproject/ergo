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

Section ErgoCalculus.

  Section Syntax.

    (** Expression *)
    Definition ergoc_expr := ErgoCodeGen.ergoc_expr.

    Record lambdac :=
      mkLambdaC
        { lambdac_params: list (string * cto_type);
          lambdac_output : cto_type;
          lambdac_throws : option cto_type;
          lambdac_emits : option cto_type;
          lambdac_body : ergoc_expr; }.

    (** Clause *)
    Record ergoc_clause :=
      mkClauseC
        { clausec_name : string;
          clausec_lambda : lambdac; }.

    (** Function *)
    Record ergoc_function :=
      mkFuncC
        { functionc_name : string;
          functionc_lambda : lambdac; }.
    
    (** Contract *)
    Record ergoc_contract :=
      mkContractC
        { contractc_name : string;
          contractc_template : string;
          contractc_clauses : list ergoc_clause; }.

    (** Declaration *)
    Inductive ergoc_declaration :=
    | ECExpr : ergoc_expr -> ergoc_declaration
    | ECGlobal : string -> ergoc_expr -> ergoc_declaration
    | ECFunc : ergoc_function -> ergoc_declaration
    | ECContract : ergoc_contract -> ergoc_declaration.
    
    (** Package. *)
    Record ergoc_package :=
      mkPackageC
        { packagec_namespace : string;
          packagec_declarations : list ergoc_declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End ErgoCalculus.

