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

Require Import ErgoSpec.Common.Utils.EUtil.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EImport.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Backend.ErgoBackend.

Section Ergo.

  (** Expression *)

  Inductive ergo_expr_desc :=
  | EThisContract : ergo_expr_desc (**r this contract *)
  | EThisClause : ergo_expr_desc (**r this clause *)
  | EThisState : ergo_expr_desc (**r this state *)
  | EVar : string -> ergo_expr_desc (**r variable *)
  | EConst : ErgoData.data -> ergo_expr_desc (**r constant *)
  | EArray : list ergo_expr -> ergo_expr_desc (**r array constructor *) 
  | EUnaryOp : ErgoOps.Unary.op -> ergo_expr -> ergo_expr_desc (**r unary operator *)
  | EBinaryOp : ErgoOps.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr_desc (**r binary operator *)
  | EIf : ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr_desc (**r conditional *)
  | ELet : string -> option ergo_type -> ergo_expr -> ergo_expr -> ergo_expr_desc (**r local variable binding *)
  | ERecord : list (string * ergo_expr) -> ergo_expr_desc (**r create a new record *)
  | ENew : name_ref -> list (string * ergo_expr) -> ergo_expr_desc (**r create a new concept/object *)
  | ECallFun : string -> list ergo_expr -> ergo_expr_desc (**r function call *)
  | EMatch : ergo_expr -> list (ergo_pattern * ergo_expr) -> ergo_expr -> ergo_expr_desc (**r match-case *)
  | EForeach : list (string * ergo_expr)
               -> option ergo_expr -> ergo_expr -> ergo_expr_desc (**r foreach with optional where *)
  with ergo_expr :=
  | EExpr : location -> ergo_expr_desc -> ergo_expr.

  Definition expr_loc (e:ergo_expr) : location :=
    match e with
    | EExpr loc _ => loc
    end.
  Definition expr_desc (e:ergo_expr) : ergo_expr_desc :=
    match e with
    | EExpr _ ed => ed
   end.
  Definition mk_expr (loc:location) (ed:ergo_expr_desc) : ergo_expr :=
    EExpr loc ed.
  
  (** Statement *)
  Inductive ergo_stmt_desc :=
  | SReturn : ergo_expr -> ergo_stmt_desc
  | SFunReturn : ergo_expr -> ergo_stmt_desc
  | SThrow : ergo_expr -> ergo_stmt_desc
  | SCallClause : string -> list ergo_expr -> ergo_stmt_desc (**r clause call *)
  | SSetState : ergo_expr -> ergo_stmt -> ergo_stmt_desc
  | SEmit : ergo_expr -> ergo_stmt -> ergo_stmt_desc
  | SLet : string -> option ergo_type -> ergo_expr -> ergo_stmt -> ergo_stmt_desc (**r local variable binding *)
  | SIf : ergo_expr -> ergo_stmt -> ergo_stmt -> ergo_stmt_desc
  | SEnforce : ergo_expr -> option ergo_stmt -> ergo_stmt -> ergo_stmt_desc (**r enforce *)
  | SMatch : ergo_expr -> (list (ergo_pattern * ergo_stmt)) -> ergo_stmt -> ergo_stmt_desc
  with ergo_stmt :=
  | EStmt : location -> ergo_stmt_desc -> ergo_stmt.

  Definition stmt_loc (e:ergo_stmt) : location :=
    match e with
    | EStmt loc _ => loc
    end.
  Definition stmt_desc (e:ergo_stmt) : ergo_stmt_desc :=
    match e with
    | EStmt _ ed => ed
    end.
  Definition mk_stmt (loc:location) (ed:ergo_stmt_desc) : ergo_stmt :=
    EStmt loc ed.
  
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
        function_location : location;
        function_lambda : lambda; }.

    (** Clause *)
    Record ergo_clause :=
      mkClause
        { clause_name : string;
          clause_location : location;
          clause_lambda : lambda; }.

    (** Contract *)
    Record ergo_contract :=
      mkContract
        { contract_name : string;
          contract_location : location;
          contract_template : ergo_type;
          contract_state : option ergo_type;
          contract_clauses : list ergo_clause; }.

    (** Declaration *)
    Inductive ergo_declaration_desc :=
    | DType : ergo_type_declaration -> ergo_declaration_desc
    | DStmt : ergo_stmt -> ergo_declaration_desc
    | DConstant : string -> ergo_expr -> ergo_declaration_desc
    | DFunc : ergo_function -> ergo_declaration_desc
    | DContract : ergo_contract -> ergo_declaration_desc
    with ergo_declaration :=
    | EDecl : location -> ergo_declaration_desc -> ergo_declaration.
 
  Definition decl_loc (d:ergo_declaration) : location :=
    match d with
    | EDecl loc _ => loc
    end.
  Definition decl_desc (d:ergo_declaration) : ergo_declaration_desc :=
    match d with
    | EDecl _ dd => dd
   end.
  Definition mk_decl (loc:location) (dd:ergo_declaration_desc) : ergo_declaration :=
    EDecl loc dd.
  
  (** Module. *)
  Record ergo_module :=
    mkModule
      { module_namespace : string;
        module_location : location;
        module_imports : list import_decl;
        module_declarations : list ergo_declaration; }.

  Section Lookup.
    Fixpoint lookup_clauses_signatures (dl:list ergo_clause) : list ergo_type_signature :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (mkErgoTypeSignature
           cl.(clause_name)
           cl.(clause_location)
           cl.(clause_lambda).(lambda_params)
           cl.(clause_lambda).(lambda_output)
           cl.(clause_lambda).(lambda_throws)
           cl.(clause_lambda).(lambda_emits)) :: lookup_clauses_signatures dl'
      end.
    
    Definition lookup_contract_signatures (c:ergo_contract) : list ergo_type_signature :=
      lookup_clauses_signatures c.(contract_clauses).

    Definition contract_of_declaration (d:ergo_declaration) : option ergo_contract :=
      match decl_desc d with
      | DContract c => Some c
      | _ => None
      end.

    Definition lookup_contracts_in_declarations (dl:list ergo_declaration) : list ergo_contract :=
      filter_some contract_of_declaration dl.

    Definition lookup_single_contract_in_declarations (dl:list ergo_declaration) : eresult ergo_contract :=
      match lookup_contracts_in_declarations dl with
      | nil => efailure (EResult.CompilationError ("Cannot compile without at least one contract"))
      | c :: nil => esuccess c
      | _ :: _ => efailure (EResult.CompilationError ("Cannot compile with more than one contract"))
      end.
      
    Definition lookup_single_contract (p:ergo_module) : eresult ergo_contract :=
      lookup_single_contract_in_declarations p.(module_declarations).

    Definition lookup_single_contract_with_state (p:ergo_module) : eresult (ergo_contract * string) :=
      eolift (fun ec =>
               elift (fun ecstate =>
                        (ec, ecstate)) (lift_default_state_name ec.(contract_state)))
            (lookup_single_contract_in_declarations p.(module_declarations)).
    
  End Lookup.

End Ergo.

