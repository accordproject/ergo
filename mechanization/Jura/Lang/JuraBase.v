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

(** Jura is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import Qcert.Common.CommonRuntime.

Section JuraBase.
  Context {fruntime:foreign_runtime}.
  (* Type for plugged-in language *)
  Context {A:Set}.
  
  Section Syntax.
    Definition package_ref := option string.

    Record class_ref :=
      mkClassRef
        { class_package : package_ref;
          class_name : string; }.

    (** Generic function closure over expressions in [A].
        All free variables in A have to be declared in the list of parameters. *)
    Record closure :=
      mkClosure
        { closure_params: list (string * option string);
          closure_output : option string;
          closure_throw : option string;
          closure_body : A; }.

    (** Clause *)
    Record clause :=
      mkClause
        { clause_name : string;
          clause_closure : closure; }.

    (** Function *)
    Record func :=
      mkFunc
        { func_name : string;
          func_closure : closure; }.
    
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
    | JExpr : A -> stmt
    | JGlobal : string -> A -> stmt
    | JImport : string -> stmt
    | JFunc : func -> stmt
    | JContract : contract -> stmt.
 
    (** Package. *)
    Record package :=
      mkPackage
        { package_name : string;
          package_statements : list stmt; }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- denotational semantics should go here *)
  End Semantics.

  Section lookup_clause.
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
      | Some c => Some c.(clause_closure).(closure_body)
      end.
    
    Definition code_from_func (f:option func) : option A :=
      match f with
      | None => None
      | Some f => Some f.(func_closure).(closure_body)
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
      | JContract c => lookup_clause_from_contract coname clname c
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

  End lookup_clause.

End JuraBase.

