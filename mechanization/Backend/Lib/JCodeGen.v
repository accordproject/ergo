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

Require Import Jura.Backend.Model.JuraBackendModel.
Require Import Jura.Backend.Model.JuraBackendRuntime.

Module JCodeGen(juramodel:JuraBackendModel).
  (* NNRC *)
  Definition jurac_expr := NNRC.nnrc.

  Definition jurac_expr_let := cNNRC.NNRCLet.

  Definition jurac_expr_unshadow := cNNRCShadow.unshadow.
  Definition jurac_expr_subst_const_to_var := cNNRCShadow.nnrc_subst_const_to_var.
  Definition jurac_expr_javascript_unshadow := NNRCtoJavaScript.nnrcToJSunshadow.

  (* JavaScript code generation *)
  Definition jurac_javascript_indent := NNRCtoJavaScript.indent.
  Definition jurac_javascript_quotel_double := NNRCtoJavaScript.quotel_double.
  Definition jurac_javascript_eol_newline := NNRCtoJavaScript.eol_newline.

  Definition jurac_javascript := CompLang.javascript.
  
  Definition jurac_expr_to_javascript := NNRCtoJavaScript.nnrcToJS.
  
  Definition jurac_expr_to_javascript_fun := NNRCtoJavaScript.nnrcToJSFun.
  
  Definition jurac_expr_to_javascript_method := NNRCtoJavaScript.nnrcToJSMethod.
  
  Definition jurac_expr_to_javascript_fun_lift
             (e:jurac_expr)
             (fname:String.string)
             (input_v:String.string)
             (init_indent:nat)
             (eol:String.string)
             (quotel:String.string) : jurac_javascript :=
    cNNRC.lift_nnrc_core
        (fun e => NNRCtoJavaScript.nnrcToJSFun input_v e init_indent eol quotel (input_v::nil) fname)
        (NNRC.nnrc_to_nnrc_core e).

End JCodeGen.

