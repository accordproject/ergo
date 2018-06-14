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

  Definition cl1 : ergo_clause :=
    mkClause "helloworld"
             (mkLambda
                (("request", CTOClassRef (AbsoluteRef "Request"))::nil)
                (CTOClassRef (AbsoluteRef "Response"))
                None
                None
                (SReturn (EVar "request"))).

  Definition c1 : ergo_contract :=
    mkContract "HelloWorld"
               "TemplateModel"
               (cl1::nil).
  
  Definition p1 : ergo_package :=
    mkPackage "org.accordproject.helloworld"
              ((EContract c1)::nil).

  (* Eval vm_compute in (ErgoCompiler.ergo_package_to_javascript nil p1). *)
End HelloWorld.

