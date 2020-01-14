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
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCT.
  Context {m : brand_model}.

  Definition tlaergo_pattern := @ergo_pattern (provenance * ergoc_type) absolute_name.
  Definition tlaergo_expr := @ergo_expr (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_stmt := @ergo_stmt (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_function := @ergo_function (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_clause := @ergo_clause (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_contract := @ergo_contract (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_declaration := @ergo_declaration (provenance * ergoc_type) provenance absolute_name.
  Definition tlaergo_module := @ergo_module (provenance * ergoc_type) provenance absolute_name.

  Section Syntax.

    (** Expression *)
    Definition ergoct_expr := tlaergo_expr.

    Definition exprct_prov_annot (e:ergoct_expr) : provenance :=
      fst (expr_annot e).
    
    Definition exprct_type_annot (e:ergoct_expr) : ergoc_type :=
      snd (expr_annot e).

    (** Function *)
    Record ergoct_function :=
      mkFuncCT
        { functionct_annot : provenance;
          functionct_sig : sigc;
          functionct_body : option ergoct_expr; }.

    (** Contract *)
    Record ergoct_contract :=
      mkContractCT
        { contractct_annot : provenance;
          contractct_clauses : list (local_name * ergoct_function); }.

    (** Declaration *)
    Inductive ergoct_declaration :=
    | DCTExpr : provenance * ergoc_type -> ergoct_expr -> ergoct_declaration
    | DCTConstant : provenance * ergoc_type -> absolute_name -> option laergo_type -> ergoct_expr -> ergoct_declaration
    | DCTFunc : provenance -> absolute_name -> ergoct_function -> ergoct_declaration
    | DCTContract : provenance -> absolute_name -> ergoct_contract -> ergoct_declaration.

    Definition ergoct_declaration_type d :=
      match d with
      | DCTExpr (_,t) _ => Some t
      | DCTConstant (_,t) _ _ _ => Some t
      | DCTFunc _ _ _ => None
      | DCTContract _ _ _ => None
      end.
    
    (** Module. *)
    Record ergoct_module :=
      mkModuleCT
        { modulect_annot : provenance;
          modulect_namespace : string;
          modulect_declarations : list ergoct_declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)

  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.

End ErgoCT.
