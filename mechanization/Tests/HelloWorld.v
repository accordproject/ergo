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
Require Import List.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Compiler.ErgoCompiler.

Section HelloWorld.
  Open Scope string_scope.
  
  (*
package org.accordproject.helloworld

contract HelloWorld over TemplateModel {
   // Simple Clause
   clause helloworld(request Request) Response {
     return new Response{ output: "Hello " ++ contract.name ++ " (" ++ request.input ++ ")" }
  }
}
*)

  Definition cl1 : lrergo_clause :=
    mkClause dummy_location
             "helloworld"
             (mkErgoTypeSignature
                dummy_location
                (("request", ErgoTypeClassRef dummy_location (None,"Request"))::nil)
                (ErgoTypeClassRef dummy_location (None,"Response"))
                None
                None)
             (Some (SReturn dummy_location (EVar dummy_location "request"))).

  Definition c1 : lrergo_contract :=
    mkContract dummy_location
               "HelloWorld"
               (ErgoTypeClassRef dummy_location (None,"TemplateModel"))
               None
               (cl1::nil).
  
  Definition p1 : lrergo_module :=
    mkModule dummy_location
             "org.accordproject.helloworld"
             nil
             (DContract dummy_location c1::nil).

  (* Eval vm_compute in (ErgoCompiler.ergo_module_to_javascript nil p1). *)
End HelloWorld.

