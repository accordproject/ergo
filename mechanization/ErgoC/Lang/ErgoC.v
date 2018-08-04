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

(** ErgoC is an intermediate language for the Ergo compiler in which:
- Clauses have been resolved to functions
- This* expressions have been eliminated
- Foreach expressions have only one dimension and no condition
- Match expressions have only two branches *)

(** * Abstract Syntax *)

Require Import String.
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoC.

  Section Syntax.

    (** Expression *)
    Definition ergoc_expr := laergo_expr.

    Record sigc :=
      mkSigC
        { sigc_params: list (string * laergo_type);
          sigc_output : laergo_type; }.

    (** Function *)
    Record ergoc_function :=
      mkFuncC
        { functionc_annot : provenance;
          functionc_sig : sigc;
          functionc_body : option ergoc_expr; }.

    (** Contract *)
    Record ergoc_contract :=
      mkContractC
        { contractc_annot : provenance;
          contractc_clauses : list (local_name * ergoc_function); }.

    (** Declaration *)
    Inductive ergoc_declaration :=
    | DCExpr : provenance -> ergoc_expr -> ergoc_declaration
    | DCConstant : provenance -> absolute_name -> option laergo_type -> ergoc_expr -> ergoc_declaration
    | DCFunc : provenance -> absolute_name -> ergoc_function -> ergoc_declaration
    | DCContract : provenance -> absolute_name -> ergoc_contract -> ergoc_declaration.

    (** Module. *)
    Record ergoc_module :=
      mkModuleC
        { modulec_annot : provenance;
          modulec_namespace : string;
          modulec_declarations : list ergoc_declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)

  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.

End ErgoC.
