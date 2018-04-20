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

(** Ergo calculus is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EError.
Require Import ErgoSpec.Common.CTO.CTO.

Section ErgoCalculusBase.
  (* Type for plugged-in language *)
  Context {A:Set}.

  Section Syntax.
    (** Generic function lambda over expressions in [A].
        All free variables in A have to be declared in the list of parameters. *)
    Definition ergoc_lambda {m:brand_relation} : Set := @closure A ErgoType.etype.

    (** Contract table *)

    Record ergoc_contract {m:brand_relation} :=
      mkCalcContract
        { calc_contract_params : list (string * ErgoType.etype);
          calc_contract_functions : list (string * ergoc_lambda); }.
    
    (** Clause *)
    Record clause :=
      mkClause
        { clause_name : string;
          clause_lambda : lambda; }.

    (** Function *)
    Record func :=
      mkFunc
        { func_name : string;
          func_lambda : lambda; }.
    
    (** Declaration *)
    Inductive declaration :=
    | Clause : clause -> declaration
    | Func : func -> declaration.
    
    (** Contract *)
    Record contract :=
      mkContract
        { contract_name : string;
          contract_template : string;
          contract_declarations : list declaration; }.

    (** Statement *)
    Inductive stmt :=
    | EType : cto_declaration -> stmt
    | EExpr : A -> stmt
    | EGlobal : string -> A -> stmt
    | EImport : string -> stmt
    | EFunc : func -> stmt
    | EContract : contract -> stmt.
 
    (** Package. *)
    Record package :=
      mkPackage
        { package_namespace : option string;
          package_statements : list stmt; }.

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

    Definition lookup_from_func (clname:string) (c:func) : option func :=
      if (string_dec clname c.(func_name))
      then Some c
      else None.

    Definition code_from_clause (c:option clause) : option A :=
      match c with
      | None => None
      | Some c => Some c.(clause_lambda).(lambda_body)
      end.
    
    Definition code_from_func (f:option func) : option A :=
      match f with
      | None => None
      | Some f => Some f.(func_lambda).(lambda_body)
      end.
    
    Definition lookup_code_from_clause (clname:string) (c:clause) : option A :=
      code_from_clause (lookup_from_clause clname c).

    Definition lookup_code_from_func (clname:string) (c:func) : option A :=
      code_from_func (lookup_from_func clname c).

    Definition lookup_clause_from_declaration (clname:string) (d:declaration) : option clause :=
      match d with
      | Clause c => lookup_from_clause clname c
      | Func f => None
      end.

    Definition lookup_clause_from_declarations (clname:string) (dl:list declaration) : option clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_clause_from_declaration clname d
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
        lookup_clause_from_declarations clname c.(contract_declarations)
      end.

    Definition lookup_clause_from_statement (coname:string) (clname:string) (d:stmt) : option clause :=
      match d with
      | EContract c => lookup_clause_from_contract coname clname c
      | _ => None
      end.

    Definition lookup_clause_from_statements
               (coname:string) (clname:string) (sl:list stmt) : option clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_clause_from_statement coname clname d
           end
        ) sl None.
    
    Definition lookup_clause_from_package
               (coname:string) (clname:string) (p:package) : option clause :=
      lookup_clause_from_statements coname clname p.(package_statements).

    Definition signature : Set := (string * list (string * option cto_type)).

    Require Import List.
    Fixpoint lookup_declarations_signatures (dl:list declaration) : list signature :=
      match dl with
      | nil => nil
      | Clause cl :: dl' =>
        (cl.(clause_name), cl.(clause_lambda).(lambda_params)) :: lookup_declarations_signatures dl'
      | Func f :: dl' =>
        (f.(func_name), f.(func_lambda).(lambda_params)) :: lookup_declarations_signatures dl'
      end.
    
    Definition lookup_contract_signatures (c:contract) : list signature :=
      lookup_declarations_signatures c.(contract_declarations).
    
    Fixpoint lookup_statements_signatures (sl:list stmt) : list signature :=
      match sl with
      | nil => nil
      | EType _ :: sl' => lookup_statements_signatures sl'
      | EExpr _ :: sl' => lookup_statements_signatures sl'
      | EGlobal _ _ :: sl' => lookup_statements_signatures sl'
      | EImport _ :: sl' => lookup_statements_signatures sl'
      | EFunc f :: sl' =>
        (f.(func_name), f.(func_lambda).(lambda_params)) :: lookup_statements_signatures sl'
      | EContract c :: sl' =>
        lookup_contract_signatures c ++ lookup_statements_signatures sl'
      end.
    
    Fixpoint lookup_statements_signatures_for_contract (oconame:option string) (sl:list stmt) : list signature :=
      match sl with
      | nil => nil
      | EType _ :: sl' => lookup_statements_signatures_for_contract oconame sl'
      | EExpr _ :: sl' => lookup_statements_signatures_for_contract oconame sl'
      | EGlobal _ _ :: sl' => lookup_statements_signatures_for_contract oconame sl'
      | EImport _ :: sl' => lookup_statements_signatures_for_contract oconame sl'
      | EFunc f :: sl' => lookup_statements_signatures_for_contract oconame sl'
      | EContract c :: sl' =>
        match oconame with
        | None =>
            lookup_contract_signatures c (* XXX Only returns signatures in first contract *)
        | Some coname =>
          if (string_dec c.(contract_name) coname)
          then
            lookup_contract_signatures c (* XXX Assumes single contract with given name *)
          else
            lookup_statements_signatures_for_contract oconame sl'
        end
      end.
    
    Definition lookup_package_signatures_for_contract (oconame:option string) (p:package) : list signature :=
      lookup_statements_signatures_for_contract oconame p.(package_statements).
    
    Definition lookup_package_signatures (p:package) : list signature :=
      lookup_statements_signatures p.(package_statements).

    Fixpoint lookup_statements_dispatch (name:string) (sl:list stmt) : eresult (cto_type * cto_type * func) :=
      match sl with
      | nil => dispatch_lookup_error
      | EType _ :: sl' => lookup_statements_dispatch name sl'
      | EExpr _ :: sl' => lookup_statements_dispatch name sl'
      | EGlobal _ _ :: sl' => lookup_statements_dispatch name sl'
      | EImport _ :: sl' => lookup_statements_dispatch name sl'
      | EFunc f :: sl' =>
        if (string_dec f.(func_name) name)
        then
          let flambda := f.(func_lambda) in
          let request :=
              match flambda.(lambda_params) with
              | nil => dispatch_parameter_error
              | (_,Some reqtype) :: _ => esuccess reqtype
              | _ :: _ => esuccess (CTOClassRef (mkClassRef None "Request"%string))
              end
          in
          let response :=
              match flambda.(lambda_output) with
              | Some resptype => resptype
              | None => (CTOClassRef (mkClassRef None "Response"%string))
              end
          in
          jlift (fun request => (request, response, f)) request
        else lookup_statements_dispatch name sl'
      | EContract c :: sl' => lookup_statements_dispatch name sl'
      end.

    Definition lookup_dispatch (name:string) (p:package) : eresult (cto_type * cto_type * func) :=
      lookup_statements_dispatch name p.(package_statements).
    
  End lookup.

End ErgoBase.

