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
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Compiler.ErgoCompiler.
Require Import ErgoSpec.Compiler.ErgoDriver.
Require Import ErgoSpec.Translation.ErgoCompContext. 
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Backend.Lib.ECType.

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
             (Some (SReturn dummy_provenance (EVar dummy_provenance (None,"request")))).

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
                    ::nil).

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
      accordproject_base_namespace
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
      accordproject_base_namespace
      nil
      (cto_typed_top::nil).

  Definition ctos : list lrergo_input := InputCTO cto_hl::nil.
  
  Definition ergo_stdlib : lrergo_module :=
    mkModule
      dummy_provenance "" "" accordproject_stdlib_namespace (DType dummy_provenance ergo_typed_top::nil).
  Definition  mls:= ergo_stdlib :: nil.

  Definition ergos : list ergo_input := InputErgo ergo_stdlib :: nil.
  Definition inputs (p:lrergo_module) : list ergo_input :=
    List.app (List.app ctos ergos) (InputErgo p::nil).

End HelloWorld.

