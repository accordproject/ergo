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

Require Import Qcert.JavaScriptAst.Lang.JavaScriptAst.
Require Import Qcert.Driver.CompDriver.
Require Import ErgoSpec.Version.
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.QLib.

Section ErgoNNRCtoJavaScript.
  Local Open Scope string_scope.
  Local Open Scope nstring_scope.

  Context {bm:brand_model}.

  (** Top-level expression *)
  Definition javascript_of_expression
             (e:nnrc_expr)                  (* expression to translate *)
             (t : nat)                      (* next available unused temporary *)
             (i : nat)                      (* indentation level *)
             (eol:nstring)                   (* Choice of end of line character *)
             (quotel:nstring)                (* Choice of quote character *)
    : nstring
    := QcertCodeGen.nnrc_expr_to_ejavascript e.

  (** Top-level constant *)
  Definition javascript_of_constant
             (v:string)                     (* constant name *)
             (bind:nnrc_expr)               (* expression computing the constant *)
             (t : nat)                      (* next available unused temporary *)
             (i : nat)                      (* indentation level *)
             (eol:nstring)                   (* Choice of end of line character *)
             (quotel:nstring)                (* Choice of quote character *)
    : QcertCodeGen.ejavascript
    := 
      let s1 := QcertCodeGen.nnrc_expr_to_ejavascript bind in
      let v0 : string := ("v"%string ++ v) in
      s1 +++ (EmitUtil.indent i) +++ ^"var " +++ ^v0 +++ ^" = <STUB>;" +++ eol.

  (** Single method *)
  Definition javascript_method_of_body
             (e:nnrc_expr)
             (fname:string)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    let input_v := "context"%string in
    QcertCodeGen.nnrc_expr_to_javascript_method e (QcertCodeGen.javascript_identifier_sanitizer fname)
                                                (input_v::nil).

  (** Single function *)
  Definition javascript_function_of_body
             (e:nnrc_expr)
             (fname:string)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    let input_v := "context"%string in
    let init_indent := 0 in
    QcertCodeGen.nnrc_expr_to_javascript_fun_lift e (QcertCodeGen.javascript_identifier_sanitizer fname) input_v.

  Definition javascript_function_of_nnrc_function
             (f:nnrc_function)
             (tname:option string)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    let fname := function_name_in_table tname f.(functionn_name) in
    javascript_function_of_body f.(functionn_lambda).(lambdan_body) fname eol quotel.

  Definition javascript_functions_of_nnrc_functions
             (fl:list nnrc_function)
             (tname:option string)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    nstring_multi_append eol (fun f => javascript_function_of_nnrc_function f tname eol quotel) fl.

  Definition javascript_method_of_nnrc_function
             (f:nnrc_function)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    let fname := f.(functionn_name) in
    javascript_method_of_body f.(functionn_lambda).(lambdan_body) fname eol quotel.
    
  Definition javascript_methods_of_nnrc_functions
             (fl:list nnrc_function)
             (tname:string)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    nstring_multi_append eol (fun f => javascript_method_of_nnrc_function f eol quotel) fl.

  Definition es5_of_nnrc_function_table
             (ft:nnrc_function_table)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    (* let tname := QcertCodeGen.javascript_identifier_sanitizer ft.(function_tablen_name) in *)
    let tname := None in
    javascript_functions_of_nnrc_functions ft.(function_tablen_funs) tname eol quotel +++ eol.

  Definition es6_of_nnrc_function_table
             (ft:nnrc_function_table)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    let tname := QcertCodeGen.javascript_identifier_sanitizer ft.(function_tablen_name) in
    ^"class " +++ ^tname +++ ^" {" +++ eol
              +++ (javascript_methods_of_nnrc_functions ft.(function_tablen_funs) tname eol quotel) +++ eol
              +++ ^"}" +++ eol.

  Definition javascript_of_nnrc_function_table
             (version:jsversion)
             (ft:nnrc_function_table)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    match version with
    | ES5 => es5_of_nnrc_function_table ft eol quotel
    | ES6 => es6_of_nnrc_function_table ft eol quotel
    end.

  Definition preamble (eol:nstring) : nstring :=
    ^"" +++ ^"/* Generated using ergoc version " +++ ^ergo_version +++ ^" */" +++ eol
        +++ ^"'use strict';" +++ eol
        +++ ^"/*eslint-disable no-unused-vars*/" +++ eol
        +++ ^"/*eslint-disable no-undef*/" +++ eol
        +++ ^"/*eslint-disable no-var*/" +++ eol
        +++ eol.

  Definition postamble (eol:nstring) :=
    ^"" +++ eol
        +++ ^"/*eslint-enable no-unused-vars*/" +++ eol
        +++ ^"/*eslint-enable no-undef*/" +++ eol
         +++ eol.
    
  Definition javascript_of_declaration
             (version:jsversion)
             (s : nnrc_declaration)   (* statement to translate *)
             (t : nat)                (* next available unused temporary *)
             (i : nat)                (* indentation level *)
             (eol : nstring)
             (quotel : nstring)
    : QcertCodeGen.ejavascript          (* JavaScript statements for computing result *)
    :=
      match s with
      | DNExpr e => javascript_of_expression e t i eol quotel
      | DNConstant v e => javascript_of_constant v e t i eol quotel
      | DNFunc f => javascript_function_of_nnrc_function f None eol quotel
      | DNFuncTable ft => javascript_of_nnrc_function_table version ft eol quotel
      end.

  Definition javascript_of_declarations
             (version:jsversion)
             (sl : list nnrc_declaration) (* statements to translate *)
             (t : nat)                    (* next available unused temporary *)
             (i : nat)                    (* indentation level *)
             (eol : nstring)
             (quotel : nstring)
    : QcertCodeGen.ejavascript
    := let proc_one
             (s:nnrc_declaration)
             (acc:QcertCodeGen.ejavascript) : QcertCodeGen.ejavascript :=
           let s1:= javascript_of_declaration version s 1 i eol quotel in
           (acc +++ s1) (* XXX Ignores e1! *)
       in
       fold_right proc_one (^"") sl.

  Definition javascript_of_inheritance
             (inheritance:list (string * string))
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    ^"" +++ ^"var inheritance = " +++ eol
        +++ (QcertCodeGen.inheritanceToJS inheritance)
        +++ ^";" +++ eol
        +++ eol.
  
  Definition nnrc_module_to_javascript
             (version:jsversion)
             (inheritance: list (string*string))
             (p:nnrc_module)
             (eol:nstring)
             (quotel:nstring) : QcertCodeGen.ejavascript :=
    (preamble eol) +++ eol
                   +++ (javascript_of_inheritance inheritance eol quotel)
                   +++ (javascript_of_declarations version p.(modulen_declarations) 0 0 eol quotel)
                   +++ (postamble eol).

  Definition nnrc_module_to_javascript_top
             (version:jsversion)
             (inheritance: list (string*string))
             (p:nnrc_module) : QcertCodeGen.ejavascript :=
    nnrc_module_to_javascript version inheritance p EmitUtil.neol_newline EmitUtil.nquotel_double.

End ErgoNNRCtoJavaScript.

