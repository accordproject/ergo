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
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoCalculus.

  Section Syntax.

    (** Expression *)
    Definition ergoc_expr := laergo_expr.
    Definition ergoc_type := laergo_type.

    Record lambdac :=
      mkLambdaC
        { lambdac_params: list (string * ergoc_type);
          lambdac_output : ergoc_type;
          lambdac_body : ergoc_expr; }.

    (** Function *)
    Record ergoc_function :=
      mkFuncC
        { functionc_annot : location;
          functionc_name : string;
          functionc_lambda : lambdac; }.

    (** Contract *)
    Record ergoc_contract :=
      mkContractC
        { contractc_annot : location;
          contractc_name : string;
          contractc_clauses : list ergoc_function; }.

    (** Declaration *)
    Inductive ergoc_declaration :=
    | DCExpr : location -> ergoc_expr -> ergoc_declaration
    | DCConstant : location -> string -> ergoc_expr -> ergoc_declaration
    | DCFunc : location -> ergoc_function -> ergoc_declaration
    | DCContract : location -> ergoc_contract -> ergoc_declaration.

    (** Module. *)
    Record ergoc_module :=
      mkModuleC
        { modulec_annot : location;
          modulec_namespace : string;
          modulec_declarations : list ergoc_declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End ErgoCalculus.

