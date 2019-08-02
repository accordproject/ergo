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
Require Import List.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoC.

  Section Syntax.

    (** Expression *)
    Definition ergoc_expr := laergo_expr.

    Record sigc :=
      mkSigC
        { sigc_params: list (string * laergo_type);
          sigc_output : option laergo_type; }.

    (** Function *)
    Record ergoc_function :=
      mkFuncC
        { functionc_annot : provenance;
          functionc_sig : sigc;
          functionc_body : option ergoc_expr; }.

    Definition bodyc_annot (f:ergoc_function) : provenance :=
      match f.(functionc_body) with
      | None => f.(functionc_annot)
      | Some e => expr_annot e
      end.
    
    (** Contract *)
    Record ergoc_contract :=
      mkContractC
        { contractc_annot : provenance;
          contractc_template : laergo_type;
          contractc_state : option laergo_type;
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

  Section Lookup.
    Fixpoint lookup_clausec_request_signatures (dl:list (local_name * ergoc_function)) : list (local_name * sigc) :=
      match dl with
      | nil => nil
      | (n,f) :: dl' =>
        match f.(functionc_sig).(sigc_params) with
        | this_contract::this_state::this_emit::((name,ErgoTypeClassRef _ _)::nil) =>
          (n,f.(functionc_sig)) :: lookup_clausec_request_signatures dl'
        | _ =>
          lookup_clausec_request_signatures dl'
        end
      end.
      
    Definition lookup_contractc_request_signatures (c:ergoc_contract) : list (local_name * sigc) :=
      lookup_clausec_request_signatures c.(contractc_clauses).

  End Lookup.
  
  Section Semantics.
    (* XXX Nothing yet -- relational semantics should go here *)

  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.

End ErgoC.
