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
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculustoJavaScript.
  Local Open Scope string_scope.

  Definition function_name_of_contract_clause_name (coname:option string) (clname:string) : string :=
    match coname with
    | None => clname
    | Some coname => coname ++ "_" ++ clname
    end.

  (** Global expression *)
  Definition javascript_of_expression
             (e:ergoc_expr)                  (* expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.ergoc_javascript
      * ErgoCodeGen.ergoc_javascript
      * nat
    := ErgoCodeGen.ergoc_expr_javascript_unshadow e t i eol quotel nil nil.

  (** Global variable *)
  Definition javascript_of_global
             (v:string)                      (* global variable name *)
             (bind:ergoc_expr)               (* expression for the global variable to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.ergoc_javascript
      * ErgoCodeGen.ergoc_javascript
      * nat
    := 
      let '(s1, e1, t2) := ErgoCodeGen.ergoc_expr_to_javascript bind t i eol quotel nil in
      let v0 := "v" ++ v in
      (s1 ++ (ErgoCodeGen.ergoc_javascript_indent i) ++ "var " ++ v0 ++ " = " ++ e1 ++ ";" ++ eol,
       v0,
       t2).

  (** Single method *)
  Definition javascript_method_of_body
             (e:ergoc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let input_v := "context" in
    ErgoCodeGen.ergoc_expr_to_javascript_method input_v e 1 eol quotel (input_v::nil) fname.

  (** Single method *)
  Definition javascript_function_of_body
             (e:ergoc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let input_v := "context" in
    let init_indent := 0 in
    ErgoCodeGen.ergoc_expr_to_javascript_fun_lift e fname input_v init_indent eol quotel.

  Definition javascript_function_of_ergo_clause
             (c:ergoc_clause)
             (coname:option string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let fname := function_name_of_contract_clause_name coname c.(clausec_name) in
    javascript_function_of_body c.(clausec_lambda).(lambdac_body) fname eol quotel.
    
  Definition javascript_function_of_ergo_func
             (f:ergoc_function)
             (coname:option string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let fname := function_name_of_contract_clause_name coname f.(functionc_name) in
    javascript_function_of_body f.(functionc_lambda).(lambdac_body) fname eol quotel ++ eol.
    
  Definition javascript_method_of_ergo_clause
             (c:ergoc_clause)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let fname := c.(clausec_name) in
    javascript_method_of_body c.(clausec_lambda).(lambdac_body) fname eol quotel.
    
  Definition javascript_method_of_ergo_func
             (f:ergoc_function)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let fname := f.(functionc_name) in
    javascript_method_of_body f.(functionc_lambda).(lambdac_body) fname eol quotel.

  Definition javascript_of_clause_list
             (cl:list ergoc_clause)
             (coname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    multi_append eol (fun c => javascript_method_of_ergo_clause c eol quotel) cl.

  Definition javascript_of_contract
             (c:ergoc_contract)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let coname := c.(contractc_name) in
    "class " ++ coname ++ " {" ++ eol
             ++ (javascript_of_clause_list c.(contractc_clauses) coname eol quotel) ++ eol
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
             (s : ergoc_declaration)       (* statement to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.ergoc_javascript         (* JavaScript statements for computing result *)
      * ErgoCodeGen.ergoc_javascript       (* JavaScript expression holding result *)
      * nat                                (* next available unused temporary *)
    :=
      match s with
      | ECExpr e => javascript_of_expression e t i eol quotel
      | ECGlobal v e => javascript_of_global v e t i eol quotel
      | ECFunc f =>
        (javascript_function_of_ergo_func f None eol quotel,"null",t)
      | ECContract c =>
        (javascript_of_contract c eol quotel,"null",t)
      end.

  Definition javascript_of_declarations
             (sl : list ergoc_declaration) (* statements to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.ergoc_javascript
    := let proc_one
             (s:ergoc_declaration)
             (acc:ErgoCodeGen.ergoc_javascript * nat) : ErgoCodeGen.ergoc_javascript * nat :=
           let '(s0, t0) := acc in
           let '(s1, e1, t1) := javascript_of_declaration s t0 i eol quotel in
           (s0 ++ s1,
            t1) (* XXX Ignores e1! *)
       in
       let '(sn, tn) := fold_right proc_one ("",t) sl in
       sn.

  Definition ergoc_package_to_javascript
             (p:ergoc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    (preamble eol) ++ eol
                   ++ (javascript_of_declarations p.(packagec_declarations) 0 0 eol quotel)
                   ++ (postamble eol).
  
  Definition ergoc_package_to_javascript_top
             (p:ergoc_package) : ErgoCodeGen.ergoc_javascript :=
    ergoc_package_to_javascript p ErgoCodeGen.ergoc_javascript_eol_newline ErgoCodeGen.ergoc_javascript_quotel_double.

End ErgoCalculustoJavaScript.

