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
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
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

  Definition cl1 :=
    mkClause "helloworld"
             (mkClosure
                (("request", Some (CTOClassRef (mkClassRef None "Request")))::nil)
                (Some (CTOClassRef (mkClassRef None "Response")))
                None
                (EVar "request")).

  Definition c1 :=
    mkContract "HelloWorld"
               "TemplateModel"
               ((Clause cl1)::nil).
  
  Definition p1 :=
    mkPackage (Some "org.accordproject.helloworld")
              ((EContract c1)::nil).

  (* Eval vm_compute in (ErgoCompiler.javascript_from_ergo_package_with_dispatch None p1). *)
End HelloWorld.

