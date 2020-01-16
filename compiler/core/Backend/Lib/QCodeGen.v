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
Require Import Qcert.Utils.Utils.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.EJson.EJsonRuntime.
Require Import Qcert.Driver.CompLang.
Require Import Qcert.Driver.CompDriver.

(* Require Import ErgoSpec.Utils.Misc. *)
Require Import ErgoSpec.Backend.Lib.QBackendModel.
Require Import ErgoSpec.Backend.Lib.QBackendRuntime.
Require Import ErgoSpec.Backend.Lib.QNNRCtoJavaScript.

Module QCodeGen(ergomodel:QBackendModel).
  Local Open Scope list_scope.
  Local Open Scope nstring_scope.
  (* NNRC *)
  Definition nnrc_expr := NNRC.nnrc.

  (* Definition nnrc_optim := CompDriver.nnrc_optim_default. *)
  Definition nnrc_optim (x:nnrc_expr) : nnrc_expr := x.
  
  Definition nnrc_expr_let := cNNRC.NNRCLet.

  Definition nnrc_expr_java_unshadow := NNRCtoJava.nnrcToJavaunshadow.

  (* JavaScript code generation *)
  Definition eindent := EmitUtil.indent.
  Definition equotel_double := EmitUtil.nquotel_double.
  Definition eeol_newline := EmitUtil.neol_newline.

  Definition javascript_identifier_sanitizer := EmitUtil.jsIdentifierSanitize.
  
  Definition ejavascript := CompLang.javascript.

  Definition nnrc_expr_to_ejavascript {bm:brand_model} (e:nnrc_expr) : ejavascript :=
    nnrc_expr_to_javascript nil None "test" e.

  Definition nnrc_expr_to_javascript_method
             {bm:brand_model}
             (e:nnrc_expr) (fname:string) (input_vs:list string) :=
    nnrc_expr_to_javascript input_vs None fname e.

  Definition nnrc_expr_to_javascript_fun_lift
             {bm:brand_model}
             (e:nnrc_expr)
             (fname:String.string)
             (input_v:String.string) : ejavascript :=
    nnrc_expr_to_javascript (input_v::nil) None fname e.

  Definition inheritanceToJS (h:list (string*string)) : nstring :=
    ^(ejsonStringify
        EmitUtil.quotel_double
        (ejarray
           (List.map (fun x => ejobject (("sub"%string,ejstring (fst x))
                                           :: ("sup"%string, (ejstring (snd x))) :: nil)) h))).

  (* Java code generation *)
  Definition java := CompLang.java.
  Definition java_identifier_sanitizer := EmitUtil.javaIdentifierSanitize.
  Definition nnrc_expr_to_java := NNRCtoJava.nnrcToJava.

  (* XXX Should be fixed Qcert-side *)
  Definition nnrc_expr_to_java_method
             (input_v:String.string)
             (e:nnrc_expr)
             (i:nat)
             (eol:nstring)
             (quotel:nstring)
             (ivs:list (String.string * nstring))
    := let e := cNNRCShadow.closeFreeVars "_" java_identifier_sanitizer (cNNRC.NNRCVar input_v) e (List.map fst ivs) in (* XXX This line is a patch for a bug in Q*cert code-gen for Java - should be moved there *)
       NNRCtoJava.nnrcToJavaFun
         i input_v e eol quotel ivs.

  (** java_data -- Internally data is kept as JSON *)
  Definition java_data := Java.java_json.
  Definition mk_java_data := Java.mk_java_json.
  Definition from_java_data : java_data -> nstring := Java.from_java_json.

End QCodeGen.
