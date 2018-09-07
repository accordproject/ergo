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

(* Require Import ErgoSpec.Common.Utils.Misc. *)
Require Import ErgoSpec.Common.Utils.Misc.
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Ast.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.

Section Ergo.
  Section Ast.
    Context {A:Set}. (* Type for annotations *)
    Context {N:Set}. (* Type for names *)
  
    (** Expression *)

    Inductive ergo_expr :=
    | EThisContract : A -> ergo_expr (**r this contract *)
    | EThisClause : A -> ergo_expr (**r this clause *)
    | EThisState : A -> ergo_expr (**r this state *)
    | EVar : A -> string -> ergo_expr (**r variable *)
    | EConst : A -> ErgoData.data -> ergo_expr (**r constant *)
    | ENone : A -> ergo_expr (**r none *)
    | ESome : A -> ergo_expr -> ergo_expr (**r some(e) *)
    | EArray : A -> list ergo_expr -> ergo_expr (**r array constructor *) 
    | EUnaryOp : A -> ErgoOps.Unary.op -> ergo_expr -> ergo_expr (**r unary operator *)
    | EBinaryOp : A -> ErgoOps.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr (**r binary operator *)
    | EIf : A -> ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr (**r conditional *)
    | ELet : A -> string -> option (@ergo_type A N) -> ergo_expr -> ergo_expr -> ergo_expr (**r local variable binding *)
    | ERecord : A -> list (string * ergo_expr) -> ergo_expr (**r create a new record *)
    | ENew : A -> N -> list (string * ergo_expr) -> ergo_expr (**r create a new concept/object *)
    | ECallFun : A -> string -> list ergo_expr -> ergo_expr (**r function call *)
    | ECallFunInGroup : A -> N -> string -> list ergo_expr -> ergo_expr (**r call function in group *)
    | EMatch : A -> ergo_expr -> list (@ergo_pattern A N * ergo_expr) -> ergo_expr -> ergo_expr (**r match-case *)
    | EForeach : A -> list (string * ergo_expr)
                 -> option ergo_expr -> ergo_expr -> ergo_expr (**r foreach with optional where *)
    .

    Definition expr_annot (e:ergo_expr) : A :=
      match e with
      | EThisContract a => a
      | EThisClause a => a
      | EThisState a => a
      | EVar a _ => a
      | EConst a _ => a
      | ENone a => a
      | ESome a _ => a
      | EArray a _ => a
      | EUnaryOp a _ _ => a
      | EBinaryOp a _ _ _ => a
      | EIf a _ _ _ => a
      | ELet a _ _ _ _ => a
      | ERecord a _ => a
      | ENew a _ _ => a
      | ECallFun a _ _ => a
      | ECallFunInGroup a _ _ _ => a
      | EMatch a _ _ _ => a
      | EForeach a _ _ _ => a
      end.
    
    (** Statement *)
    Inductive ergo_stmt :=
    | SReturn : A -> ergo_expr -> ergo_stmt
    | SFunReturn : A -> ergo_expr -> ergo_stmt
    | SThrow : A -> ergo_expr -> ergo_stmt
    | SCallClause : A -> ergo_expr -> string -> list ergo_expr -> ergo_stmt (**r clause call *)
    | SSetState : A -> ergo_expr -> ergo_stmt -> ergo_stmt
    | SEmit : A -> ergo_expr -> ergo_stmt -> ergo_stmt
    | SLet : A -> string -> option (@ergo_type A N) -> ergo_expr -> ergo_stmt -> ergo_stmt (**r local variable *)
    | SIf : A -> ergo_expr -> ergo_stmt -> ergo_stmt -> ergo_stmt
    | SEnforce : A -> ergo_expr -> option ergo_stmt -> ergo_stmt -> ergo_stmt (**r enforce *)
    | SMatch : A -> ergo_expr -> (list (@ergo_pattern A N * ergo_stmt)) -> ergo_stmt -> ergo_stmt
    .

    Definition stmt_annot (e:ergo_stmt) : A :=
      match e with
      | SReturn a _ => a
      | SFunReturn a _ => a
      | SThrow a _ => a
      | SCallClause a _ _ _ => a
      | SSetState a _ _ => a
      | SEmit a _ _ => a
      | SLet a _ _ _ _ => a
      | SIf a _ _ _ => a
      | SEnforce a _ _ _ => a
      | SMatch a _ _ _ => a
      end.
    
    (** Function *)
    Record ergo_function :=
      mkFunc
        { function_annot : A;
          function_sig : @ergo_type_signature A N;
          function_body : option ergo_expr; }.

    Definition body_annot (f:ergo_function) : A :=
      match f.(function_body) with
      | None => f.(function_annot)
      | Some e => expr_annot e
      end.
    
    (** Clause *)
    Record ergo_clause :=
      mkClause
        { clause_annot : A;
          clause_name : local_name;
          clause_sig : @ergo_type_signature A N;
          clause_body : option ergo_stmt; }.

    (** Contract *)
    Record ergo_contract :=
      mkContract
        { contract_annot : A;
          contract_template : (@ergo_type A N);
          contract_state : option (@ergo_type A N);
          contract_clauses : list ergo_clause; }.

    (** Declaration *)
    Inductive ergo_declaration :=
    | DNamespace : A -> namespace_name -> ergo_declaration
    | DImport : A -> @import_decl A -> ergo_declaration
    | DType : A -> @ergo_type_declaration A N -> ergo_declaration
    | DStmt : A -> ergo_stmt -> ergo_declaration
    | DConstant : A -> local_name -> option (@ergo_type A N) -> ergo_expr -> ergo_declaration
    | DFunc : A -> local_name -> ergo_function -> ergo_declaration
    | DContract : A -> local_name -> ergo_contract -> ergo_declaration
    | DSetContract : A -> N -> ergo_expr -> ergo_declaration
    .
    
    Definition decl_annot (d:ergo_declaration) : A :=
      match d with
      | DNamespace a _ => a
      | DImport a _ => a
      | DType a _ => a
      | DStmt a _ => a
      | DConstant a _ _ _ => a
      | DFunc a _ _ => a
      | DContract a _ _ => a
      | DSetContract a _ _ => a
      end.

    (** Module. *)
    Record ergo_module :=
      mkModule
        { module_annot : A;
          module_file : string;
          module_namespace : namespace_name;
          module_declarations : list ergo_declaration; }.

    Inductive ergo_input :=
    | InputErgo : ergo_module -> ergo_input
    | InputCTO : @cto_package A N -> ergo_input.

  End Ast.

  Definition rergo_expr {A} := @ergo_expr A relative_name.
  Definition rergo_stmt {A} := @ergo_stmt A relative_name.
  Definition rergo_function {A} := @ergo_function A relative_name.
  Definition rergo_clause {A} := @ergo_clause A relative_name.
  Definition rergo_contract {A} := @ergo_contract A relative_name.
  Definition rergo_declaration {A} := @ergo_declaration A relative_name.
  Definition rergo_module {A} := @ergo_module A relative_name.
  Definition rergo_input {A} := @ergo_input A relative_name.

  Definition aergo_expr {A} := @ergo_expr A absolute_name.
  Definition aergo_stmt {A} := @ergo_stmt A absolute_name.
  Definition arergo_function {A} := @ergo_function A absolute_name.
  Definition arergo_clause {A} := @ergo_clause A absolute_name.
  Definition arergo_contract {A} := @ergo_contract A absolute_name.
  Definition arergo_declaration {A} := @ergo_declaration A absolute_name.
  Definition arergo_module {A} := @ergo_module A absolute_name.

  Definition lrergo_expr := @ergo_expr provenance relative_name.
  Definition lrergo_stmt := @ergo_stmt provenance relative_name.
  Definition lrergo_function := @ergo_function provenance relative_name.
  Definition lrergo_clause := @ergo_clause provenance relative_name.
  Definition lrergo_contract := @ergo_contract provenance relative_name.
  Definition lrergo_declaration := @ergo_declaration provenance relative_name.
  Definition lrergo_module := @ergo_module provenance relative_name.
  Definition lrergo_input := @ergo_input provenance relative_name.

  Definition laergo_expr := @ergo_expr provenance absolute_name.
  Definition laergo_stmt := @ergo_stmt provenance absolute_name.
  Definition laergo_function := @ergo_function provenance absolute_name.
  Definition laergo_clause := @ergo_clause provenance absolute_name.
  Definition laergo_contract := @ergo_contract provenance absolute_name.
  Definition laergo_declaration := @ergo_declaration provenance absolute_name.
  Definition laergo_module := @ergo_module provenance absolute_name.

  Section Lookup.
    Fixpoint lookup_clauses_signatures (dl:list laergo_clause) : list (local_name * ergo_type_signature) :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (cl.(clause_name),cl.(clause_sig)) :: lookup_clauses_signatures dl'
      end.
      
    Definition lookup_contract_signatures (c:ergo_contract) : list (local_name * ergo_type_signature) :=
      lookup_clauses_signatures c.(contract_clauses).

    Definition contract_of_declaration (d:laergo_declaration) : option (absolute_name * laergo_contract) :=
      match d with
      | DContract _ cn c => Some (cn, c)
      | _ => None
      end.

    Definition lookup_contracts_in_declarations (dl:list laergo_declaration)
      : list (absolute_name * laergo_contract) :=
      filter_some contract_of_declaration dl.

    Definition lookup_single_contract_in_declarations
               (prov:provenance) (dl:list laergo_declaration) : eresult (absolute_name * laergo_contract) :=
      match lookup_contracts_in_declarations dl with
      | nil => should_have_one_contract_error prov
      | c :: nil => esuccess c
      | _ :: _ => should_have_one_contract_error prov
      end.

    Definition lookup_single_contract (p:laergo_module) : eresult (absolute_name * laergo_contract) :=
      lookup_single_contract_in_declarations p.(module_annot) p.(module_declarations).

    Definition lookup_single_contract_with_state (p:laergo_module)
      : eresult ((absolute_name * laergo_contract) * string) :=
      eolift (fun ec =>
                elift (fun ecstate =>
                         (ec, ecstate)) (lift_default_state_name (snd ec).(contract_state)))
             (lookup_single_contract_in_declarations p.(module_annot) p.(module_declarations)).
  End Lookup.

  Section TypeDeclarations.
    Fixpoint get_type_decls (decls:list laergo_declaration) : list laergo_type_declaration :=
      match decls with
      | nil => nil
      | DType _ td :: rest => td :: (get_type_decls rest)
      | _ :: rest => get_type_decls rest
      end.

    Definition module_get_type_decls (m:laergo_module) : list laergo_type_declaration :=
      get_type_decls m.(module_declarations).

    Definition modules_get_type_decls (m:list laergo_module) : list laergo_type_declaration :=
      List.concat (List.map module_get_type_decls m).
  End TypeDeclarations.
  
End Ergo.

