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
Require Import List.

Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EError.
Require Import ErgoSpec.Common.Utils.EImport.
Require Import ErgoSpec.Common.CTO.CTO.

Section ErgoBase.
  (* Type for plugged-in language *)
  Context {A:Set}.
  Context {B:Set}.

  Section Syntax.
    (** Generic function closure over expressions in [A].
        All free variables in A have to be declared in the list of parameters. *)
    Record lambda :=
      mkLambda
        { lambda_params: list (string * cto_type);
          lambda_output : cto_type;
          lambda_throw : option string;
          lambda_body : B; }.

    (** Function *)
    Record function :=
      mkFunc
        { function_name : string;
          function_lambda : lambda; }.
    
    (** Clause *)
    Record clause :=
      mkClause
        { clause_name : string;
          clause_lambda : lambda; }.

    (** Contract *)
    Record contract :=
      mkContract
        { contract_name : string;
          contract_template : string;
          contract_clauses : list clause; }.

    (** Declaration *)
    Inductive declaration :=
    | EType : cto_declaration -> declaration
    | EExpr : A -> declaration
    | EGlobal : string -> A -> declaration
    | EImport : import_decl -> declaration
    | EFunc : function -> declaration
    | EContract : contract -> declaration.
 
    (** Package. *)
    Record package :=
      mkPackage
        { package_namespace : string;
          package_declarations : list declaration; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- denotational semantics should go here *)
  End Semantics.

  Section Lookup.
    Definition signature : Set := (string * list (string * cto_type) * cto_type).

    Fixpoint lookup_clauses_signatures (dl:list clause) : list signature :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (cl.(clause_name), cl.(clause_lambda).(lambda_params), cl.(clause_lambda).(lambda_output)) :: lookup_clauses_signatures dl'
      end.
    
    Definition lookup_contract_signatures (c:contract) : list signature :=
      lookup_clauses_signatures c.(contract_clauses).
    
    Fixpoint lookup_contracts_in_declarations (dl:list declaration) : list contract :=
      match dl with
      | nil => nil
      | EType _ :: dl' => lookup_contracts_in_declarations dl'
      | EExpr _ :: dl' => lookup_contracts_in_declarations dl'
      | EGlobal _ _ :: dl' => lookup_contracts_in_declarations dl'
      | EImport _ :: dl' => lookup_contracts_in_declarations dl'
      | EFunc f :: dl' => lookup_contracts_in_declarations dl'
      | EContract c :: dl' => c :: lookup_contracts_in_declarations dl'
      end.

    Definition lookup_single_contract_in_declarations (dl:list declaration) : eresult contract :=
      match lookup_contracts_in_declarations dl with
      | nil => efailure (CompilationError ("Cannot compile without at least one contract"))
      | c :: nil => esuccess c
      | _ :: _ => efailure (CompilationError ("Cannot compile with more than one contract"))
      end.
      
    Definition lookup_single_contract (p:package) : eresult contract :=
      lookup_single_contract_in_declarations p.(package_declarations).
    
  End Lookup.

End ErgoBase.

