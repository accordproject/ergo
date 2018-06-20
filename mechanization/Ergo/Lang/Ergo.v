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
Require Import EquivDec.

Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EImport.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Backend.ErgoBackend.

Section Ergo.

  (** Expression *)
  Inductive ergo_expr :=
  | EThisContract : ergo_expr (**r this contract *)
  | EThisClause : ergo_expr (**r this clause *)
  | EThisState : ergo_expr (**r this state *)
  | EVar : string -> ergo_expr (**r variable *)
  | EConst : ErgoData.data -> ergo_expr (**r constant *)
  | EArray : list ergo_expr -> ergo_expr (**r array constructor *) 
  | EUnaryOp : ErgoOps.Unary.op -> ergo_expr -> ergo_expr (**r unary operator *)
  | EBinaryOp : ErgoOps.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr (**r binary operator *)
  | EIf : ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr (**r conditional *)
  | ELet : string -> option ergo_type -> ergo_expr -> ergo_expr -> ergo_expr (**r local variable binding *)
  | ERecord : list (string * ergo_expr) -> ergo_expr (**r create a new record *)
  | ENew : name_ref -> list (string * ergo_expr) -> ergo_expr (**r create a new concept/object *)
  | ECallFun : string -> list ergo_expr -> ergo_expr (**r function call *)
  | EMatch : ergo_expr -> list (ergo_pattern * ergo_expr) -> ergo_expr -> ergo_expr (**r match-case *)
  | EForeach : list (string * ergo_expr)
               -> option ergo_expr -> ergo_expr -> ergo_expr (**r foreach with optional where *)
  | ELiftError : ergo_expr -> ergo_expr -> ergo_expr
  .

  (** Statement *)
  Inductive ergo_stmt :=
  | SReturn : ergo_expr -> ergo_stmt
  | SFunReturn : ergo_expr -> ergo_stmt
  | SThrow : ergo_expr -> ergo_stmt
  | SCallClause : string -> list ergo_expr -> ergo_stmt (**r clause call *)
  | SSetState : ergo_expr -> ergo_stmt -> ergo_stmt
  | SEmit : ergo_expr -> ergo_stmt -> ergo_stmt
  | SLet : string -> option ergo_type -> ergo_expr -> ergo_stmt -> ergo_stmt (**r local variable binding *)
  | SIf : ergo_expr -> ergo_stmt -> ergo_stmt -> ergo_stmt
  | SEnforce : ergo_expr -> option ergo_stmt -> ergo_stmt -> ergo_stmt (**r enforce *)
  | SMatch : ergo_expr -> (list (ergo_pattern * ergo_stmt)) -> ergo_stmt -> ergo_stmt.

  (** Function *)
  Record lambda :=
    mkLambda
      { lambda_params: list (string * ergo_type);
        lambda_output : ergo_type;
        lambda_throws : option ergo_type;
        lambda_emits : option ergo_type;
        lambda_body : ergo_stmt; }.

  Record ergo_function :=
    mkFunc
      { function_name : string;
        function_lambda : lambda; }.

    (** Clause *)
    Record ergo_clause :=
      mkClause
        { clause_name : string;
          clause_lambda : lambda; }.

    (** Contract *)
    Record ergo_contract :=
      mkContract
        { contract_name : string;
          contract_template : ergo_type;
          contract_state : option ergo_type;
          contract_clauses : list ergo_clause; }.

    (** Declaration *)
    Inductive ergo_declaration :=
    | EType : ergo_type_declaration -> ergo_declaration
    | EExpr : ergo_expr -> ergo_declaration
    | EGlobal : string -> ergo_expr -> ergo_declaration
    | EFunc : ergo_function -> ergo_declaration
    | EContract : ergo_contract -> ergo_declaration.
 
    (** Module. *)
    Record ergo_module :=
      mkModule
        { module_namespace : string;
          module_imports : list import_decl;
          module_declarations : list ergo_declaration; }.

  Section Lookup.
    Fixpoint lookup_clauses_signatures (dl:list ergo_clause) : list ergo_type_signature :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (mkErgoTypeSignature
           cl.(clause_name)
           cl.(clause_lambda).(lambda_params)
           cl.(clause_lambda).(lambda_output)
           cl.(clause_lambda).(lambda_throws)
           cl.(clause_lambda).(lambda_emits)) :: lookup_clauses_signatures dl'
      end.
    
    Definition lookup_contract_signatures (c:ergo_contract) : list ergo_type_signature :=
      lookup_clauses_signatures c.(contract_clauses).
    
    Fixpoint lookup_contracts_in_declarations (dl:list ergo_declaration) : list ergo_contract :=
      match dl with
      | nil => nil
      | EType _ :: dl' => lookup_contracts_in_declarations dl'
      | EExpr _ :: dl' => lookup_contracts_in_declarations dl'
      | EGlobal _ _ :: dl' => lookup_contracts_in_declarations dl'
      | EFunc f :: dl' => lookup_contracts_in_declarations dl'
      | EContract c :: dl' => c :: lookup_contracts_in_declarations dl'
      end.

    Definition lookup_single_contract_in_declarations (dl:list ergo_declaration) : eresult ergo_contract :=
      match lookup_contracts_in_declarations dl with
      | nil => efailure (EResult.CompilationError ("Cannot compile without at least one contract"))
      | c :: nil => esuccess c
      | _ :: _ => efailure (EResult.CompilationError ("Cannot compile with more than one contract"))
      end.
      
    Definition lookup_single_contract (p:ergo_module) : eresult ergo_contract :=
      lookup_single_contract_in_declarations p.(module_declarations).
    
  End Lookup.

End Ergo.

