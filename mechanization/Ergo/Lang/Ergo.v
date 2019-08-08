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
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.

Section Ergo.
  Section Ast.
    Context {A:Set}. (* For expression annotations *)
    Context {A':Set}. (* For type annotations *)
    Context {N:Set}. (* For names *)

    (** Expression *)
    Inductive ergo_expr :=
    | EThis : A -> ergo_expr (**r generic this *)
    | EThisContract : A -> ergo_expr (**r this contract *)
    | EThisClause : A -> ergo_expr (**r this clause *)
    | EThisState : A -> ergo_expr (**r this state *)
    | EVar : A -> N -> ergo_expr (**r variable *)
    | EConst : A -> ErgoData.data -> ergo_expr (**r constant *)
    | EText : A -> list ergo_expr -> ergo_expr (**r embedded text *)
    | ENone : A -> ergo_expr (**r none *)
    | ESome : A -> ergo_expr -> ergo_expr (**r some(e) *)
    | EArray : A -> list ergo_expr -> ergo_expr (**r array constructor *)
    | EUnaryOperator : A -> ergo_unary_operator -> ergo_expr -> ergo_expr (**r unary operator *)
    | EBinaryOperator : A -> ergo_binary_operator -> ergo_expr -> ergo_expr -> ergo_expr (**r binary operator *)
    | EUnaryBuiltin : A -> ErgoOps.Unary.op -> ergo_expr -> ergo_expr (**r unary builtin *)
    | EBinaryBuiltin : A -> ErgoOps.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr (**r binary builtin *)
    | EIf : A -> ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr (**r conditional *)
    | ELet : A -> string -> option (@ergo_type A' N) -> ergo_expr -> ergo_expr -> ergo_expr (**r local variable binding *)
    | EPrint : A -> ergo_expr -> ergo_expr -> ergo_expr (**r print *)
    | ERecord : A -> list (string * ergo_expr) -> ergo_expr (**r create a new record *)
    | ENew : A -> N -> list (string * ergo_expr) -> ergo_expr (**r create a new concept/object *)
    | ECallFun : A -> N -> list ergo_expr -> ergo_expr (**r function call *)
    | ECallFunInGroup : A -> N -> string -> list ergo_expr -> ergo_expr (**r call function in group *)
    | EMatch : A -> ergo_expr -> list (@ergo_pattern A N * ergo_expr) -> ergo_expr -> ergo_expr (**r match-case *)
    | EForeach : A -> list (string * ergo_expr)
                 -> option ergo_expr -> ergo_expr -> ergo_expr (**r foreach with optional where *)
    .

    Definition expr_annot (e:ergo_expr) : A :=
      match e with
      | EThis a => a
      | EThisContract a => a
      | EThisClause a => a
      | EThisState a => a
      | EVar a _ => a
      | EConst a _ => a
      | EText a _ => a
      | ENone a => a
      | ESome a _ => a
      | EArray a _ => a
      | EUnaryOperator a _ _ => a
      | EBinaryOperator a _ _ _ => a
      | EUnaryBuiltin a _ _ => a
      | EBinaryBuiltin a _ _ _ => a
      | EIf a _ _ _ => a
      | ELet a _ _ _ _ => a
      | EPrint a _ _ => a
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
    | SCallContract : A -> ergo_expr -> list ergo_expr -> ergo_stmt (**r contract call *)
    | SSetState : A -> ergo_expr -> ergo_stmt -> ergo_stmt
    | SEmit : A -> ergo_expr -> ergo_stmt -> ergo_stmt
    | SLet : A -> string -> option (@ergo_type A N) -> ergo_expr -> ergo_stmt -> ergo_stmt (**r local variable *)
    | SPrint : A -> ergo_expr -> ergo_stmt -> ergo_stmt (**r local variable *)
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
      | SCallContract a _ _ => a
      | SSetState a _ _ => a
      | SEmit a _ _ => a
      | SLet a _ _ _ _ => a
      | SPrint a _ _ => a
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
          module_prefix : string;
          module_namespace : namespace_name;
          module_declarations : list ergo_declaration; }.

    Inductive ergo_input :=
    | InputErgo : ergo_module -> ergo_input
    | InputCTO : @cto_package A N -> ergo_input.

  End Ast.

  Definition rergo_expr {A} {A'} := @ergo_expr A A' relative_name.
  Definition rergo_stmt {A} {A'} := @ergo_stmt A A' relative_name.
  Definition rergo_function {A} {A'} := @ergo_function A A' relative_name.
  Definition rergo_clause {A} {A'} := @ergo_clause A A' relative_name.
  Definition rergo_contract {A} {A'} := @ergo_contract A A' relative_name.
  Definition rergo_declaration {A} {A'} := @ergo_declaration A A' relative_name.
  Definition rergo_module {A} {A'} := @ergo_module A A' relative_name.
  Definition rergo_input {A} {A'} := @ergo_input A A' relative_name.

  Definition aergo_expr {A} {A'} := @ergo_expr A A' absolute_name.
  Definition aergo_stmt {A} {A'} := @ergo_stmt A A' absolute_name.
  Definition arergo_function {A} {A'} := @ergo_function A A' absolute_name.
  Definition arergo_clause {A} {A'} := @ergo_clause A A' absolute_name.
  Definition arergo_contract {A} {A'} := @ergo_contract A A' absolute_name.
  Definition arergo_declaration {A} {A'} := @ergo_declaration A A' absolute_name.
  Definition arergo_module {A} {A'} := @ergo_module A A' absolute_name.
  Definition arergo_input {A} {A'} := @ergo_input A A' absolute_name.

  Definition lrergo_expr := @ergo_expr provenance provenance relative_name.
  Definition lrergo_stmt := @ergo_stmt provenance provenance relative_name.
  Definition lrergo_function := @ergo_function provenance provenance relative_name.
  Definition lrergo_clause := @ergo_clause provenance provenance relative_name.
  Definition lrergo_contract := @ergo_contract provenance provenance relative_name.
  Definition lrergo_declaration := @ergo_declaration provenance provenance relative_name.
  Definition lrergo_module := @ergo_module provenance provenance relative_name.
  Definition lrergo_input := @ergo_input provenance provenance relative_name.

  Definition laergo_expr := @ergo_expr provenance provenance absolute_name.
  Definition laergo_stmt := @ergo_stmt provenance provenance absolute_name.
  Definition laergo_function := @ergo_function provenance provenance absolute_name.
  Definition laergo_clause := @ergo_clause provenance provenance absolute_name.
  Definition laergo_contract := @ergo_contract provenance provenance absolute_name.
  Definition laergo_declaration := @ergo_declaration provenance provenance absolute_name.
  Definition laergo_module := @ergo_module provenance provenance absolute_name.
  Definition laergo_input := @ergo_input provenance provenance absolute_name.

  Section Lookup.
    Fixpoint lookup_clause_signatures (dl:list laergo_clause) : list (local_name * ergo_type_signature) :=
      match dl with
      | nil => nil
      | cl :: dl' =>
        (cl.(clause_name),cl.(clause_sig)) :: lookup_clause_signatures dl'
      end.

    Definition lookup_contract_signatures (c:ergo_contract) : list (local_name * ergo_type_signature) :=
      lookup_clause_signatures c.(contract_clauses).

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
      | c :: nil => esuccess c nil
      | _ :: _ => should_have_one_contract_error prov
      end.

    Definition lookup_single_contract (p:laergo_module) : eresult (absolute_name * laergo_contract) :=
      lookup_single_contract_in_declarations p.(module_annot) p.(module_declarations).

    Definition contract_name_of_decl (d:laergo_declaration) : option string :=
      match d with
      | DNamespace _ _
      | DImport _ _
      | DType _ _
      | DStmt _ _
      | DConstant _ _ _ _
      | DFunc _ _ _
      | DSetContract _ _ _ => None
      | DContract _ an _ => Some an
      end.

    Definition lift_contract_name_of_decl (d:laergo_declaration) (acc:option string) : option string :=
      match acc with
      | None => contract_name_of_decl d
      | Some _ => acc
      end.

    Definition default_contract_name_from_decls (dl:list ergo_declaration) : option string :=
      fold_right lift_contract_name_of_decl None dl.

    Definition default_contract_name (m:ergo_module) : option string :=
      default_contract_name_from_decls m.(module_declarations).
    
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


  Section Enums.
    Fixpoint either_from_enum_values (enum_values:list string) : list (string * data) :=
      match enum_values with
      | nil => nil
      | x :: enum_values' =>
        let new_values := either_from_enum_values enum_values' in
        (x, dleft (dstring x)) :: (map (fun xy => (fst xy, dright (snd xy))) new_values)
      end.

    Definition globals_from_enum prov (enum:string * list string) : list (string * laergo_expr * data) :=
      let (enum_name, enum_values) := enum in
      map (fun xy =>
             let d := dbrand (enum_name::nil) (snd xy) in
             (fst xy, (EConst prov d), d))
          (either_from_enum_values enum_values).

  End Enums.

End Ergo.

