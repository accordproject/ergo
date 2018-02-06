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
  
  Section Syntax.
    (* Type for plugged-in language *)
    Context {A:Set}.

    Definition package_ref := option string.

    Record class_ref :=
      mkClassRef
        { class_package : package_ref;
          class_name : string; }.

    (** Clause *)
    Record clause :=
      mkClause
        { clause_name : string;
          clause_params : list (string * string);
          clause_output : string;
          clause_throw : option string;
          clause_code : A; }.
    
    (** Declaration *)
    Inductive declaration :=
    | Clause : clause -> declaration.
    
    (** Contract *)
    Record contract :=
      mkContract
        { contract_name : string;
          contract_template : string;
          contract_declarations : list declaration; }.
    
    (** A Jura package. *)
   
    Record package :=
      mkPackage
        { package_name : string;
          package_imports : list string;
          package_contract : contract }.

  End Syntax.

  Section Semantics.
    (* XXX Nothing yet -- denotational semantics should go here *)
  End Semantics.
End JuraBase.

