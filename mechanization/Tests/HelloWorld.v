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
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Compiler.ErgoCompiler.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.

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
    mkClause dummy_provenance
             "helloworld"
             (mkErgoTypeSignature
                dummy_provenance
                (("request", ErgoTypeClassRef dummy_provenance (None,"Request"))::nil)
                (Some (ErgoTypeClassRef dummy_provenance (None,"Response")))
                None)
             (Some (SReturn dummy_provenance (EVar dummy_provenance "request"))).

  Definition c1 : lrergo_contract :=
    mkContract dummy_provenance
               (ErgoTypeClassRef dummy_provenance (None,"TemplateModel"))
               None
               (cl1::nil).
  
  Definition ergo_funcd1 : lrergo_function :=
    mkFunc
      dummy_provenance
      (mkErgoTypeSignature
         dummy_provenance
         (("req",ErgoTypeBoolean dummy_provenance)::nil)
         (Some (ErgoTypeBoolean dummy_provenance))
         None)
      None.
    
  Definition ergo_funcd2 : lrergo_function :=
    mkFunc
      dummy_provenance
      (mkErgoTypeSignature
         dummy_provenance
         nil
         (Some (ErgoTypeBoolean dummy_provenance))
         None)
      (Some (ECallFun dummy_provenance (None,"addFee") nil)).

  Definition ergo_clause2 : lrergo_clause :=
    mkClause
      dummy_provenance
      "addFee2"
      (mkErgoTypeSignature
         dummy_provenance
         (("request", ErgoTypeClassRef dummy_provenance (None,"Request"))::nil)
         (Some (ErgoTypeClassRef dummy_provenance (None,"Response")))
         None)
      (Some (SReturn dummy_provenance (ECallFun dummy_provenance (None,"addFee") nil))).

  Definition ergo_contractd1 : lrergo_contract :=
    mkContract
      dummy_provenance
      (ErgoTypeBoolean dummy_provenance)
      None
      (ergo_clause2::nil).

  Definition p1 : lrergo_module :=
    mkModule dummy_provenance
             ""
             ""
             "org.accordproject.helloworld"
             (DFunc dummy_provenance "addFee" ergo_funcd1
                    ::DContract dummy_provenance "HelloWorld" c1
                    ::DContract dummy_provenance "MyContract" ergo_contractd1::nil).

  Definition cto_typed_tm : lrcto_declaration :=
    mkCTODeclaration
      dummy_provenance
      "TemplateModel"
      (CTOConcept
         false
         None
         (("x",(CTOBoolean dummy_provenance))::nil)).
  Definition cto_typed_rq : lrcto_declaration :=
    mkCTODeclaration
      dummy_provenance
      "Request"
      (CTOConcept
         false
         None
         (("x",(CTOBoolean dummy_provenance))::nil)).
  Definition cto_typed_rs : lrcto_declaration :=
    mkCTODeclaration
      dummy_provenance
      "Response"
      (CTOConcept
         false
         None
         (("x",(CTOBoolean dummy_provenance))::nil)).
  Definition cto_model : lrcto_package :=
    mkCTOPackage
      dummy_provenance
      ""
      ""
      hyperledger_namespace
      nil
      (cto_typed_tm::cto_typed_rq::cto_typed_rs::nil).

  Definition cto_typed_top : lrcto_declaration :=
    mkCTODeclaration
      dummy_provenance
      "top"
      (CTOConcept
         false
         None
         (("x",(CTOBoolean dummy_provenance))::nil)).
  Definition cto_hl : lrcto_package :=
    mkCTOPackage
      dummy_provenance
      ""
      ""
      hyperledger_namespace
      nil
      (cto_typed_top::nil).
  Definition ctos : list lrcto_package := cto_hl::cto_model::nil.
  
  Definition ergo_stdlib : lrergo_module :=
    mkModule
      dummy_provenance "" "" stdlib_namespace (DType dummy_provenance ergo_typed_top::nil).
  Definition  mls:= ergo_stdlib :: nil.

End HelloWorld.

