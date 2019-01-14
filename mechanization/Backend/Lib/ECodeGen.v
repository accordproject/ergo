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
Require Import Qcert.Compiler.Driver.CompDriver.

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.

Require Import ErgoSpec.Backend.Lib.ENNRCtoJavaScript.

Module ECodeGen(ergomodel:ErgoBackendModel).
  (* NNRC *)
  Definition nnrc_expr := NNRC.nnrc.

  (* Definition nnrc_optim := CompDriver.nnrc_optim_default. *)
  Definition nnrc_optim (x:nnrc_expr) : nnrc_expr := x.
  
  Definition nnrc_expr_let := cNNRC.NNRCLet.

  Definition nnrc_expr_java_unshadow := NNRCtoJava.nnrcToJavaunshadow.

  (* JavaScript code generation *)
  Definition javascript_indent := ENNRCtoJavaScript.indent.
  Definition javascript_quotel_double := ENNRCtoJavaScript.quotel_double.
  Definition javascript_eol_newline := ENNRCtoJavaScript.eol_newline.

  Definition javascript_identifier_sanitizer := ENNRCtoJavaScript.jsIdentifierSanitize.
  
  Definition ejavascript := Misc.ejavascript.
  
  Definition nnrc_expr_javascript_unshadow n t1 t2 s1 s2 v h :=
    ENNRCtoJavaScript.nnrcToJSunshadow (nnrc_optim n) t1 t2 s1 s2 v h.
  
  Definition nnrc_expr_to_javascript n t1 t2 s1 s2 h :=
    ENNRCtoJavaScript.nnrcToJS (nnrc_optim n) t1 t2 s1 s2 h.

  Definition nnrc_expr_to_javascript_method s0 n s1 s2 ls s3 :=
    ENNRCtoJavaScript.nnrcToJSMethod s0 (nnrc_optim n) s1 s2 ls s3.

  Definition nnrc_expr_to_javascript_fun_lift
             (e:nnrc_expr)
             (fname:String.string)
             (input_v:String.string)
             (init_indent:nat)
             (eol:estring)
             (quotel:estring) : ejavascript :=
    cNNRC.lift_nnrc_core
        (fun e => ENNRCtoJavaScript.nnrcToJSFun input_v e init_indent eol quotel (input_v::nil) fname)
        (NNRC.nnrc_to_nnrc_core e).

  (* Java code generation *)
  Definition java_indent := NNRCtoJava.indent.
  Definition java_quotel_double := NNRCtoJava.quotel_double.
  Definition java_eol_newline := NNRCtoJava.eol_newline.

  Definition java_identifier_sanitizer := NNRCtoJava.javaIdentifierSanitize.
  
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
    := let e := cNNRCShadow.closeFreeVars "_" NNRCtoJava.javaIdentifierSanitize (cNNRC.NNRCVar input_v) e (List.map fst ivs) in (* XXX This line is a patch for a bug in Q*cert code-gen for Java - should be moved there *)
       NNRCtoJava.nnrcToJavaFun
         i input_v e eol quotel ivs.

  (** java_data -- Internally data is kept as JSON *)
  Definition java_data := ForeignToJava.java_json.
  Definition mk_java_data := ForeignToJava.mk_java_json.
  Definition from_java_data : java_data -> String.string := NNRCtoJava.from_java_json.

End ECodeGen.

