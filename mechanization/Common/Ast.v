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

Require Import String.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Provenance.

Section Ast.
  Section Imports.
    Section Defn.
      Context {A:Set}. (* For expression annotations *)
      Context {N:Set}. (* For names *)

      Inductive import_decl : Set :=
      | ImportAll : A -> namespace_name -> import_decl
      | ImportSelf : A -> namespace_name -> import_decl
      | ImportName : A -> namespace_name -> local_name -> import_decl.

      Definition import_annot (i:import_decl) :=
        match i with
        | ImportAll a _ => a
        | ImportSelf a _ => a
        | ImportName a _ _ => a
        end.

      Definition extends : Set := option N.
    End Defn.

    Definition limport_decl : Set := @import_decl provenance.
    
    Definition rextends : Set := @extends relative_name.
    Definition aextends : Set := @extends absolute_name.
  End Imports.

  Section Abstract.
    Definition is_abstract : Set := bool.
    
  End Abstract.

  Section Patterns.
    Section Defn.
      Local Open Scope string.

      Context {A:Set}. (* Type for annotations *)
      Context {N:Set}. (* Type for names *)
  
      Definition type_annotation : Set := option N.

      Inductive ergo_pattern :=
      | CaseData : A -> ErgoData.data -> ergo_pattern                  (**r match against value *)
      | CaseEnum : A -> N -> ergo_pattern                              (**r match against enum *)
      | CaseWildcard : A -> type_annotation -> ergo_pattern            (**r match anything *)
      | CaseLet : A -> string -> type_annotation -> ergo_pattern       (**r match against type *)
      | CaseLetOption : A -> string -> type_annotation -> ergo_pattern (**r match against type *)
      .
    End Defn.

    Definition rergo_pattern {A} := @ergo_pattern A relative_name.
    Definition aergo_pattern {A} := @ergo_pattern A absolute_name.

    Definition lrergo_pattern := @ergo_pattern provenance relative_name.
    Definition laergo_pattern := @ergo_pattern provenance absolute_name.
  End Patterns.

  Section Operators.
    Local Open Scope string.

    (** Unary operators -- Those can be overloaded *)
    Inductive ergo_unary_operator :=
    | EOpUMinus : ergo_unary_operator
    | EOpDot : string -> ergo_unary_operator
    .

    Global Instance ToString_ergo_unary_operator : ToString ergo_unary_operator
      := {toString :=
            fun (op:ergo_unary_operator) =>
              match op with
              | EOpUMinus => "-"
              | EOpDot a => "." ++ a
              end
         }.

    (** Binary operators -- Those can be overloaded *)
    Inductive ergo_binary_operator :=
    | EOpPlus : ergo_binary_operator
    | EOpMinus : ergo_binary_operator
    | EOpMultiply : ergo_binary_operator
    | EOpDivide : ergo_binary_operator
    | EOpRemainder : ergo_binary_operator
    | EOpGe : ergo_binary_operator
    | EOpGt : ergo_binary_operator
    | EOpLe : ergo_binary_operator
    | EOpLt : ergo_binary_operator
    .

    Global Instance ToString_ergo_binary_operator : ToString ergo_binary_operator
      := {toString :=
            fun (op:ergo_binary_operator) =>
              match op with
              | EOpPlus => "+"
              | EOpMinus => "-"
              | EOpMultiply => "*"
              | EOpDivide => "/"
              | EOpRemainder => "%"
              | EOpGe => ">="
              | EOpGt => ">"
              | EOpLe => "<="
              | EOpLt => "<"
              end
         }.

  End Operators.
End Ast.
