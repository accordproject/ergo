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

(** Translates ErgoNNRC to JavaScript *)

Require Import String.
Require Import List.

Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Driver.CompDriver.
Require Import ErgoSpec.Version.
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.QLib.

Section ErgoNNRCtoJavaScript.
  Local Open Scope list_scope.

  Context {bm:brand_model}.

  (** Top-level expression *)
  Definition javascript_of_expression
             (globals:list string)
             (e:nnrc_expr)                  (* expression to translate *)
    : js_ast
    := nil. (* XXX TODO -- either support or prove it is not being emitted *)

  (** Top-level constant *)
  Definition javascript_of_constant
             (globals:list string)
             (v:string)                     (* constant name *)
             (bind:nnrc_expr)               (* expression computing the constant *)
    : js_ast
    := nil. (* XXX TODO -- either support or prove it is not being emitted *)

  (** Single function *)
  Definition javascript_function_of_nnrc_function
             (globals:list string)
             (f:nnrc_function)
             (tname:option string) : js_ast :=
    let fname := QcertCodeGen.javascript_identifier_sanitizer (function_name_in_table tname f.(functionn_name)) in
    QcertCodeGen.nnrc_expr_to_javascript_function globals (fname, f.(functionn_lambda).(lambdan_body)).

  (** Single method *)
  Definition javascript_of_nnrc_function_table
             (globals:list string)
             (ft:nnrc_function_table) : js_ast :=
    let cname := QcertCodeGen.javascript_identifier_sanitizer ft.(function_tablen_name) in
    QcertCodeGen.nnrc_expr_to_javascript_function_table
      globals cname
      (List.map (fun f => (QcertCodeGen.javascript_identifier_sanitizer f.(functionn_name),
                           f.(functionn_lambda).(lambdan_body))) ft.(function_tablen_funs)).

  Definition preamble : js_ast :=
    (comment (" Generated using ergoc version " ++ ergo_version ++ " "))
      :: strictmode
      :: (comment "eslint-disable no-unused-vars")
      :: (comment "eslint-disable no-undef")
      :: (comment "eslint-disable no-var")
      :: nil.

  Definition postamble : js_ast :=
    (comment "eslint-enable no-unused-vars")
      :: (comment "eslint-enable no-undef")
      :: nil.
    
  Definition javascript_of_declaration
             (globals:list string)    (* globally known variables -- avoid list *)
             (s : nnrc_declaration)   (* statement to translate *)
    : js_ast
    :=
      match s with
      | DNExpr e => javascript_of_expression globals e
      | DNConstant v e => javascript_of_constant globals v e
      | DNFunc f => javascript_function_of_nnrc_function globals f None
      | DNFuncTable ft => javascript_of_nnrc_function_table globals ft
      end.

  Definition javascript_of_declarations
             (sl : list nnrc_declaration) (* statements to translate *)
    : js_ast
    := List.concat (List.map (javascript_of_declaration (* XXX globals *) nil) sl).

  Definition nnrc_module_to_javascript
             (inheritance: list (string*string))
             (p:nnrc_module) : js_ast :=
    preamble ++ (QcertCodeGen.javascript_of_inheritance inheritance)
             ++ (javascript_of_declarations p.(modulen_declarations))
             ++ (postamble).

  Definition nnrc_module_to_javascript_top
             (inheritance: list (string*string))
             (p:nnrc_module) : QcertCodeGen.ejavascript :=
    js_ast_to_javascript (nnrc_module_to_javascript inheritance p).

End ErgoNNRCtoJavaScript.

