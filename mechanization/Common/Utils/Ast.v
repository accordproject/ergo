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
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Provenance.

Section Ast.
  Section Imports.
    Section Defn.
      Context {A:Set}. (* Type for annotations *)
      Context {N:Set}. (* Type for names *)
  
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
  
End Ast.
