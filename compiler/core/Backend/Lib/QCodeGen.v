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
Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Translation.Lang.ImpEJsontoJavaScriptAst.
Require Import Qcert.Driver.CompLang.
Require Import Qcert.Driver.CompDriver.

(* Require Import ErgoSpec.Utils.Misc. *)
Require Import ErgoSpec.Backend.Lib.QBackendModel.
Require Import ErgoSpec.Backend.Lib.QBackendRuntime.

Module QCodeGen(ergomodel:QBackendModel).
  Local Open Scope list_scope.

  (** NNRC *)
  Section NNRC.
    Definition nnrc_expr := NNRC.nnrc.

    (* Definition nnrc_optim := CompDriver.nnrc_optim_default. *)
    Definition nnrc_optim (x:nnrc_expr) : nnrc_expr := x.
  
    Definition nnrc_expr_let := cNNRC.NNRCLet.

  End NNRC.

  Section Emit.
    (* JavaScript code generation *)
    Definition eindent := EmitUtil.indent.
    Definition equotel_double := EmitUtil.nquotel_double.
    Definition eeol_newline := EmitUtil.neol_newline.
    Definition javascript_identifier_sanitizer := EmitUtil.jsIdentifierSanitize.
  End Emit.    


  (* JavaScript code generation *)
  Section JavaScript.

    Definition ejavascript := CompLang.javascript.

    Definition nnrc_expr_to_imp_ejson
               {bm:brand_model}
               (globals:list string)
               (f:string * nnrc) : imp_ejson :=
      let (fname,fbody) := f in
      (imp_data_to_imp_ejson
         (nnrs_imp_to_imp_data
            fname
            (nnrs_to_nnrs_imp
               (nnrc_to_nnrs
                  globals fbody)))).
  
    Definition nnrc_expr_to_javascript_function
               {bm:brand_model}
               (globals:list string)
               (f:string * nnrc) : js_ast :=
      imp_ejson_to_function (nnrc_expr_to_imp_ejson globals f).
    
    Definition nnrc_expr_to_javascript_function_table
               {bm:brand_model}
               (globals:list string)
               (cname:string)
               (ftable:list (string * nnrc_expr)) : js_ast :=
      imp_ejson_table_to_topdecls cname (List.map (nnrc_expr_to_imp_ejson globals) ftable).

    Definition js_ast_to_javascript (q:js_ast) : javascript :=
      js_ast_to_javascript q.

    Definition javascript_of_inheritance (h:list (string*string)) : js_ast :=
      constdecl "inheritance"
                (ejson_to_js_ast
                   (ejarray
                      (List.map (fun x =>
                                   ejobject (("sub"%string,ejstring (fst x))
                                               :: ("sup"%string, (ejstring (snd x))) :: nil)) h))) :: nil.
  End JavaScript.

  Section Java.
    Local Open Scope nstring_scope.
    (* Java code generation *)
    Definition java := CompLang.java.
    Definition java_identifier_sanitizer := EmitUtil.javaIdentifierSanitize.
    Definition nnrc_expr_to_java := NNRCtoJava.nnrcToJava.
    Definition nnrc_expr_java_unshadow := NNRCtoJava.nnrcToJavaunshadow.

    (* XXX Should be fixed Qcert-side *)
    Definition nnrc_expr_to_java_method
               (input_v:String.string)
               (e:nnrc_expr)
               (i:nat)
               (eol:nstring)
               (quotel:nstring)
               (ivs:list (String.string * nstring))
      :=
        let e :=
            (* XXX This line is a patch for a bug in Q*cert code-gen for Java - should be moved there *)
            cNNRCShadow.closeFreeVars
              "_" java_identifier_sanitizer (cNNRC.NNRCVar input_v) e (List.map fst ivs)
        in
        NNRCtoJava.nnrcToJavaFun
          i input_v e eol quotel ivs.

    (** java_data -- Internally data is kept as JSON *)
    Definition java_data := Java.java_json.
    Definition mk_java_data := Java.mk_java_json.
    Definition from_java_data : java_data -> nstring := Java.from_java_json.
  End Java.

End QCodeGen.
