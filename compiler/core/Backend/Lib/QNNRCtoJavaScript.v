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

Require Import List.
Require Import String.
Require Import Ascii.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Qcert.Utils.Utils.
Require Import Qcert.Data.DataSystem.
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.JavaScript.JavaScriptRuntime.
Require Import Qcert.EJson.EJsonRuntime.
Require Import Qcert.Driver.CompDriver.
(* Foreign Datatypes Support *)

Require Import Qcert.Translation.Model.ForeignDataToEJson.
Require Import Qcert.Translation.Operators.ForeignToEJsonRuntime.
Require Import Qcert.Translation.Operators.ForeignToJavaScriptAst.

Local Open Scope string_scope.

Section QNNRCtoJavaScript.

  (* Context *)
  Context {ftype:foreign_type}.
  Context {fruntime:foreign_runtime}.
  Context {fejson:foreign_ejson}.
  Context {ftejson:foreign_to_ejson}.
  Context {frtejson:foreign_to_ejson_runtime}.
  Context {bm:brand_model}.
  Context {ftjsast:foreign_ejson_to_ajavascript}.

  Definition nnrc_expr_to_javascript_function constants (cname:option string) (fname:string) (e:nnrc) : js_ast :=
    imp_ejson_to_js_ast
      cname
      (imp_data_to_imp_ejson
         (nnrs_imp_to_imp_data
            fname
            (nnrs_to_nnrs_imp
               (nnrc_to_nnrs
                  constants e)))).

  Definition js_ast_to_javascript (q:js_ast) : javascript :=
    js_ast_to_javascript q.

  Definition nnrc_expr_to_javascript constants (cname:option string) (fname:string) (e:nnrc) : javascript :=
    js_ast_to_javascript (nnrc_expr_to_javascript_function constants cname fname e).

  Section CodeGenTest.
    
    Definition e_in : nnrc :=
      NNRCBinop OpRecConcat
                (NNRCUnop (UnaryOperators.OpRec "a")
                          (NNRCLet "p1"
                                   (NNRCConst (dstring "hi"))
                                   (NNRCVar "p1")))
                (NNRCUnop (OpRec "b")
                          (NNRCLet "p1"
                                   (NNRCConst (dstring "boo"))
                                   (NNRCVar "p1"))).

    Definition test_gen (e:nnrc) :=
      nnrc_expr_to_javascript nil None "foo" e.

(*    
    Eval vm_compute in (test_gen e_in).
 *)

  End CodeGenTest.
End QNNRCtoJavaScript.
