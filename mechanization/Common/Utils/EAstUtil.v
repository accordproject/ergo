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
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.

Section EAstUtil.
  Section Ast.
    Context {A:Set}. (* Type for annotations *)
    Context {N:Set}. (* Type for names *)
  
    Inductive import_decl : Set :=
    | ImportAll : A -> namespace_name -> import_decl
    | ImportSelf : A -> namespace_name -> import_decl
    | ImportName : A -> namespace_name -> local_name -> import_decl.

    Definition extends : Set := option N.

  End Ast.

  Definition limport_decl : Set := @import_decl location.
  
  Definition rextends : Set := @extends relative_name.
  Definition aextends : Set := @extends absolute_name.

End EAstUtil.
