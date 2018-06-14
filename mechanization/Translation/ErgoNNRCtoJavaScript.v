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

(** Translates contract logic to calculus *)

Require Import String.
Require Import List.
Require Import ErgoSpec.Common.Utils.EUtil.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoNNRCtoJavaScript.
  Local Open Scope string_scope.

  Definition function_name_of_contract_clause_name (coname:option string) (clname:string) : string :=
    match coname with
    | None => clname
    | Some coname => coname ++ "_" ++ clname
    end.

  (** Global expression *)
  Definition javascript_of_expression
             (e:nnrc_expr)                  (* expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.javascript
      * ErgoCodeGen.javascript
      * nat
    := ErgoCodeGen.nnrc_expr_javascript_unshadow e t i eol quotel nil nil.

  (** Global variable *)
  Definition javascript_of_global
             (v:string)                      (* global variable name *)
             (bind:nnrc_expr)               (* expression for the global variable to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.javascript
      * ErgoCodeGen.javascript
      * nat
    := 
      let '(s1, e1, t2) := ErgoCodeGen.nnrc_expr_to_javascript bind t i eol quotel nil in
      let v0 := "v" ++ v in
      (s1 ++ (ErgoCodeGen.javascript_indent i) ++ "var " ++ v0 ++ " = " ++ e1 ++ ";" ++ eol,
       v0,
       t2).

  (** Single method *)
  Definition javascript_method_of_body
             (e:nnrc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let input_v := "context" in
    ErgoCodeGen.nnrc_expr_to_javascript_method input_v e 1 eol quotel (input_v::nil) fname.

  (** Single method *)
  Definition javascript_function_of_body
             (e:nnrc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let input_v := "context" in
    let init_indent := 0 in
    ErgoCodeGen.nnrc_expr_to_javascript_fun_lift e fname input_v init_indent eol quotel.

  Definition javascript_function_of_ergo_clause
             (c:nnrc_function)
             (coname:option string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let fname := function_name_of_contract_clause_name coname c.(functionn_name) in
    javascript_function_of_body c.(functionn_lambda).(lambdan_body) fname eol quotel.

  Definition javascript_function_of_ergo_func
             (f:nnrc_function)
             (coname:option string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let fname := function_name_of_contract_clause_name coname f.(functionn_name) in
    javascript_function_of_body f.(functionn_lambda).(lambdan_body) fname eol quotel ++ eol.
    
  Definition javascript_method_of_ergo_clause
             (c:nnrc_function)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let fname := c.(functionn_name) in
    javascript_method_of_body c.(functionn_lambda).(lambdan_body) fname eol quotel.
    
  Definition javascript_method_of_ergo_func
             (f:nnrc_function)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let fname := f.(functionn_name) in
    javascript_method_of_body f.(functionn_lambda).(lambdan_body) fname eol quotel.

  Definition javascript_of_clause_list
             (cl:list nnrc_function)
             (coname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    multi_append eol (fun c => javascript_method_of_ergo_clause c eol quotel) cl.

  Definition javascript_of_contract
             (c:nnrc_contract)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let coname := c.(contractn_name) in
    "class " ++ coname ++ " {" ++ eol
             ++ (javascript_of_clause_list c.(contractn_clauses) coname eol quotel) ++ eol
             ++ "}" ++ eol.

  Definition preamble (eol:string) :=
    "" ++ "'use strict';" ++ eol
       ++ "/*eslint-disable no-unused-vars*/" ++ eol
       ++ "/*eslint-disable no-undef*/" ++ eol
       ++ "/*eslint-disable no-var*/" ++ eol
       ++ eol.

  Definition postamble (eol:string) :=
    "" ++ eol
       ++ "/*eslint-enable no-unused-vars*/" ++ eol
       ++ "/*eslint-enable no-undef*/" ++ eol
       ++ eol.
    
  Definition javascript_of_declaration
             (s : nnrc_declaration)   (* statement to translate *)
             (t : nat)                (* next available unused temporary *)
             (i : nat)                (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.javascript          (* JavaScript statements for computing result *)
      * ErgoCodeGen.javascript        (* JavaScript expression holding result *)
      * nat                           (* next available unused temporary *)
    :=
      match s with
      | ENExpr e => javascript_of_expression e t i eol quotel
      | ENGlobal v e => javascript_of_global v e t i eol quotel
      | ENFunc f => (javascript_function_of_ergo_func f None eol quotel,"null",t)
      | ENContract c => (javascript_of_contract c eol quotel,"null",t)
      end.

  Definition javascript_of_declarations
             (sl : list nnrc_declaration) (* statements to translate *)
             (t : nat)                    (* next available unused temporary *)
             (i : nat)                    (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.javascript
    := let proc_one
             (s:nnrc_declaration)
             (acc:ErgoCodeGen.javascript * nat) : ErgoCodeGen.javascript * nat :=
           let '(s0, t0) := acc in
           let '(s1, e1, t1) := javascript_of_declaration s t0 i eol quotel in
           (s0 ++ s1,
            t1) (* XXX Ignores e1! *)
       in
       let '(sn, tn) := fold_right proc_one ("",t) sl in
       sn.

  Definition nnrc_package_to_javascript
             (p:nnrc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    (preamble eol) ++ eol
                   ++ (javascript_of_declarations p.(packagen_declarations) 0 0 eol quotel)
                   ++ (postamble eol).
  
  Definition nnrc_package_to_javascript_top
             (p:nnrc_package) : ErgoCodeGen.javascript :=
    nnrc_package_to_javascript p ErgoCodeGen.javascript_eol_newline ErgoCodeGen.javascript_quotel_double.

End ErgoNNRCtoJavaScript.

