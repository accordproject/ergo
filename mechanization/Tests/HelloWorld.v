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
  
  Definition ergo_funcd1 : lrergo_function :=
    mkFunc
      dummy_location
      "addFee"
      (mkErgoTypeSignature
         dummy_location
         (("req",ErgoTypeBoolean dummy_location)::nil)
         (ErgoTypeBoolean dummy_location)
         None
         None)
      None.
    
  Definition ergo_funcd2 : lrergo_function :=
    mkFunc
      dummy_location
      "addFee2"
      (mkErgoTypeSignature
         dummy_location
         nil
         (ErgoTypeBoolean dummy_location)
         None
         None)
      (Some (SFunReturn dummy_location (ECallFun dummy_location "addFee" nil))).

  Definition ergo_clause2 : lrergo_clause :=
    mkClause
      dummy_location
      "addFee2"
      (mkErgoTypeSignature
         dummy_location
         (("request", ErgoTypeClassRef dummy_location (None,"Request"))::nil)
         (ErgoTypeClassRef dummy_location (None,"Response"))
         None
         None)
      (Some (SReturn dummy_location (ECallFun dummy_location "addFee" nil))).

  Definition ergo_contractd1 : lrergo_contract :=
    mkContract
      dummy_location
      "MyContract"
      (ErgoTypeBoolean dummy_location)
      None
      (ergo_clause2::nil).

  Definition p1 : lrergo_module :=
    mkModule dummy_location
             "org.accordproject.helloworld"
             nil
             (DFunc dummy_location ergo_funcd1
                    ::DContract dummy_location c1
                    ::DContract dummy_location ergo_contractd1::nil).

  Definition cto_typed_tm : lrcto_declaration :=
    mkCTODeclaration
      dummy_location
      "TemplateModel"
      (CTOConcept
         None
         (("x",(CTOBoolean dummy_location))::nil)).
  Definition cto_typed_rq : lrcto_declaration :=
    mkCTODeclaration
      dummy_location
      "Request"
      (CTOConcept
         None
         (("x",(CTOBoolean dummy_location))::nil)).
  Definition cto_typed_rs : lrcto_declaration :=
    mkCTODeclaration
      dummy_location
      "Response"
      (CTOConcept
         None
         (("x",(CTOBoolean dummy_location))::nil)).
  Definition cto_model : lrcto_package :=
    mkCTOPackage
      dummy_location
      hyperledger_namespace
      nil
      (cto_typed_tm::cto_typed_rq::cto_typed_rs::nil).

  Definition cto_typed_top : lrcto_declaration :=
    mkCTODeclaration
      dummy_location
      "top"
      (CTOConcept
         None
         (("x",(CTOBoolean dummy_location))::nil)).
  Definition cto_hl : lrcto_package :=
    mkCTOPackage
      dummy_location
      hyperledger_namespace
      nil
      (cto_typed_top::nil).
  Definition ctos : list lrcto_package := cto_hl::cto_model::nil.
  
  Definition ergo_stdlib : lrergo_module :=
    mkModule
      dummy_location stdlib_namespace nil (DType dummy_location ergo_typed_top::nil).
  Definition  mls:= ergo_stdlib :: nil.

  (* Compute (ErgoCompiler.ergo_module_to_javascript ctos mls p1). *)

  Definition ictos := map InputCTO ctos.
  Definition imls := map InputErgo mls.
  Definition ctxt := init_namespace_ctxt.
  Definition rmods := resolve_ergo_inputs ctxt (ictos ++ imls).
  (* Compute rmods. *)
  Definition p := eolift (fun pc => resolve_ergo_module (snd pc) p1) rmods.
  Require Import ErgoExpand.
  Require Import ErgotoErgoCalculus.
  Require Import ErgoCalculustoErgoNNRC.
  Definition p' := eolift (fun pc => expand_ergo_module (fst pc)) p.
  (* Compute p'. *)
  Definition pc := elift ergo_module_to_calculus p'.
  (* Compute pc. *)
  Definition pn := eolift (fun rmods => eolift (ergoc_module_to_nnrc (fst rmods)) pc) rmods.
  (* Compute pn. *)

End HelloWorld.

