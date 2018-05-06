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
    Record lambdaa :=
      mkLambdaA
        { lambdaa_params: list (string * cto_type);
          lambdaa_output : cto_type;
          lambdaa_throw : option string;
          lambdaa_body : A; }.

    Record lambdab :=
      mkLambdaB
        { lambdab_params: list (string * cto_type);
          lambdab_output : cto_type;
          lambdab_throw : option string;
          lambdab_body : B; }.

    (** Function *)
    Record function :=
      mkFunc
        { function_name : string;
          function_lambda : lambdaa; }.
    
    (** Clause *)
    Record clause :=
      mkClause
        { clause_name : string;
          clause_lambda : lambdab; }.

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

  Section lookup.
    (** Returns clause code *)
    Definition lookup_from_clause (clname:string) (c:clause) : option clause :=
      if (string_dec clname c.(clause_name))
      then Some c
      else None.

    Definition lookup_from_func (clname:string) (c:function) : option function :=
      if (string_dec clname c.(function_name))
      then Some c
      else None.

    Definition code_from_clause (c:option clause) : option B :=
      match c with
      | None => None
      | Some c => Some c.(clause_lambda).(lambdab_body)
      end.
    
    Definition code_from_function (f:option function) : option A :=
      match f with
      | None => None
      | Some f => Some f.(function_lambda).(lambdaa_body)
      end.
    
    Definition lookup_code_from_clause (clname:string) (c:clause) : option B :=
      code_from_clause (lookup_from_clause clname c).

    Definition lookup_code_from_func (clname:string) (c:function) : option A :=
      code_from_function (lookup_from_func clname c).

    Definition lookup_from_clauses (clname:string) (dl:list clause) : option clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_from_clause clname d
           end
        ) dl None.
    
    Definition lookup_contract_from_contract (coname:string) (c:contract) : option contract :=
      if (string_dec coname c.(contract_name))
      then Some c
      else None.

    Definition lookup_clause_from_contract
               (coname:string) (clname:string) (c:contract) : option clause :=
      match lookup_contract_from_contract coname c with
      | None => None
      | Some c =>
        lookup_from_clauses clname c.(contract_clauses)
      end.

    Definition lookup_clause_from_declaration (coname:string) (clname:string) (d:declaration) : option clause :=
      match d with
      | EContract c => lookup_clause_from_contract coname clname c
      | _ => None
      end.

    Definition lookup_clause_from_declarations
               (coname:string) (clname:string) (dl:list declaration) : option clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_clause_from_declaration coname clname d
           end
        ) dl None.
    
    Definition lookup_clause_from_package
               (coname:string) (clname:string) (p:package) : option clause :=
      lookup_clause_from_declarations coname clname p.(package_declarations).

    Definition signature : Set := (string * list (string * cto_type)).

    Fixpoint lookup_clauses_signatures (dl:list clause) : list signature :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (cl.(clause_name), cl.(clause_lambda).(lambdab_params)) :: lookup_clauses_signatures dl'
      end.
    
    Definition lookup_contract_signatures (c:contract) : list signature :=
      lookup_clauses_signatures c.(contract_clauses).
    
    Fixpoint lookup_statements_signatures (sl:list declaration) : list signature :=
      match sl with
      | nil => nil
      | EType _ :: sl' => lookup_statements_signatures sl'
      | EExpr _ :: sl' => lookup_statements_signatures sl'
      | EGlobal _ _ :: sl' => lookup_statements_signatures sl'
      | EImport _ :: sl' => lookup_statements_signatures sl'
      | EFunc f :: sl' =>
        (f.(function_name), f.(function_lambda).(lambdaa_params)) :: lookup_statements_signatures sl'
      | EContract c :: sl' =>
        lookup_contract_signatures c ++ lookup_statements_signatures sl'
      end.
    
    Fixpoint lookup_statements_signatures_for_contract (oconame:option string) (dl:list declaration) : list signature :=
      match dl with
      | nil => nil
      | EType _ :: dl' => lookup_statements_signatures_for_contract oconame dl'
      | EExpr _ :: dl' => lookup_statements_signatures_for_contract oconame dl'
      | EGlobal _ _ :: dl' => lookup_statements_signatures_for_contract oconame dl'
      | EImport _ :: dl' => lookup_statements_signatures_for_contract oconame dl'
      | EFunc f :: dl' => lookup_statements_signatures_for_contract oconame dl'
      | EContract c :: dl' =>
        match oconame with
        | None =>
            lookup_contract_signatures c (* XXX Only returns signatures in first contract *)
        | Some coname =>
          if (string_dec c.(contract_name) coname)
          then
            lookup_contract_signatures c (* XXX Assumes single contract with given name *)
          else
            lookup_statements_signatures_for_contract oconame dl'
        end
      end.
    
    Definition lookup_package_signatures_for_contract (oconame:option string) (p:package) : list signature :=
      lookup_statements_signatures_for_contract oconame p.(package_declarations).
    
    Definition lookup_package_signatures (p:package) : list signature :=
      lookup_statements_signatures p.(package_declarations).

    Fixpoint lookup_statements_dispatch (name:string) (dl:list declaration) : eresult (cto_type * cto_type * function) :=
      match dl with
      | nil => dispatch_lookup_error
      | EType _ :: dl' => lookup_statements_dispatch name dl'
      | EExpr _ :: dl' => lookup_statements_dispatch name dl'
      | EGlobal _ _ :: dl' => lookup_statements_dispatch name dl'
      | EImport _ :: dl' => lookup_statements_dispatch name dl'
      | EFunc f :: dl' =>
        if (string_dec f.(function_name) name)
        then
          let flambda := f.(function_lambda) in
          let request :=
              match flambda.(lambdaa_params) with
              | nil => dispatch_parameter_error
              | (_,reqtype) :: _ => esuccess reqtype
              end
          in
          let response := flambda.(lambdaa_output) in
          elift (fun request => (request, response, f)) request
        else lookup_statements_dispatch name dl'
      | EContract c :: dl' => lookup_statements_dispatch name dl'
      end.

    Definition lookup_dispatch (name:string) (p:package) : eresult (cto_type * cto_type * function) :=
      lookup_statements_dispatch name p.(package_declarations).
    
  End lookup.

End ErgoBase.

