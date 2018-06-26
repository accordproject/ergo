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

Require String.

Require Qcert.Compiler.Driver.CompLang.

Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.

Module ECodeGen(ergomodel:ErgoBackendModel).
  (* NNRC *)
  Definition nnrc_expr := NNRC.nnrc.

  Definition nnrc_expr_let := cNNRC.NNRCLet.

  Definition nnrc_expr_unshadow := cNNRCShadow.unshadow.
  Definition nnrc_expr_subst_const_to_var := cNNRCShadow.nnrc_subst_const_to_var.
  Definition nnrc_expr_javascript_unshadow := NNRCtoJavaScript.nnrcToJSunshadow.
  Definition nnrc_expr_java_unshadow := NNRCtoJava.nnrcToJavaunshadow.

  (* JavaScript code generation *)
  Definition javascript_indent := NNRCtoJavaScript.indent.
  Definition javascript_quotel_double := NNRCtoJavaScript.quotel_double.
  Definition javascript_eol_newline := NNRCtoJavaScript.eol_newline.

  Definition javascript_identifier_sanitizer := NNRCtoJavaScript.jsIdentifierSanitize.
  
  Definition javascript := CompLang.javascript.
  
  Definition nnrc_expr_to_javascript := NNRCtoJavaScript.nnrcToJS.
  
  Definition nnrc_expr_to_javascript_fun := NNRCtoJavaScript.nnrcToJSFun.
  
  Definition nnrc_expr_to_javascript_method := NNRCtoJavaScript.nnrcToJSMethod.
  
  Definition nnrc_expr_to_javascript_fun_lift
             (e:nnrc_expr)
             (fname:String.string)
             (input_v:String.string)
             (init_indent:nat)
             (eol:String.string)
             (quotel:String.string) : javascript :=
    cNNRC.lift_nnrc_core
        (fun e => NNRCtoJavaScript.nnrcToJSFun input_v e init_indent eol quotel (input_v::nil) fname)
        (NNRC.nnrc_to_nnrc_core e).

  (* Java code generation *)
  Definition java_indent := NNRCtoJava.indent.
  Definition java_quotel_double := NNRCtoJava.quotel_double.
  Definition java_eol_newline := NNRCtoJava.eol_newline.

  Definition java := CompLang.java.
  
  Definition nnrc_expr_to_java := NNRCtoJava.nnrcToJava.

  (* XXX Should be fixed Qcert-side *)
  Definition nnrc_expr_to_java_method
             (input_v:String.string)
             (e:nnrc_expr)
             (i:nat)
             (eol:String.string)
             (quotel:String.string)
             (ivs:list (String.string * String.string))
    := NNRCtoJava.nnrcToJavaFun
         i input_v e eol quotel ivs.

  (** java_data -- Internally data is kept as JSON *)
  Definition java_data := ForeignToJava.java_json.
  Definition mk_java_data := ForeignToJava.mk_java_json.
  Definition from_java_data : java_data -> String.string := NNRCtoJava.from_java_json.

End ECodeGen.

