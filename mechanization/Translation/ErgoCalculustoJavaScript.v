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
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculustoJavaScript.

  Definition lookup_error (coname:string) (clname:string) :=
    let msg := ("Clause " ++ clname ++ " in contract " ++ coname ++ " not found")%string in
    EResult.CompilationError msg.

  Definition lookup_clause_code_from_package
             (coname:string) (clname:string) (p:ergoc_package) : eresult ergoc_expr :=
    let clause := lookup_clause_from_package coname clname p in
    eresult_of_option (code_from_clause clause) (lookup_error coname clname).

  Section translate.
    (* Context *)
    Local Open Scope string_scope.

    Definition multi_append {A} separator (f:A -> string) (elems:list A) : string :=
      match elems with
      | nil => ""
      | e :: elems' =>
        (fold_left (fun acc e => acc ++ separator ++ (f e)) elems' (f e))%string
      end.

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
      let fname := function_name_of_contract_clause_name coname c.(clause_name) in
      javascript_function_of_body c.(clause_lambda).(lambda_body) fname eol quotel.
    
    Definition javascript_function_of_ergo_func
               (f:ergoc_function)
               (coname:option string)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      let fname := function_name_of_contract_clause_name coname f.(function_name) in
      javascript_function_of_body f.(function_lambda).(lambda_body) fname eol quotel ++ eol.
    
    Definition javascript_method_of_ergo_clause
               (c:ergoc_clause)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      let fname := c.(clause_name) in
      javascript_method_of_body c.(clause_lambda).(lambda_body) fname eol quotel.
    
    Definition javascript_method_of_ergo_func
               (f:ergoc_function)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      let fname := f.(function_name) in
      javascript_method_of_body f.(function_lambda).(lambda_body) fname eol quotel.

    Definition javascript_of_clause_list
               (cl:list clause)
               (coname:string)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      multi_append eol (fun c => javascript_method_of_ergo_clause c eol quotel) cl.

    Definition javascript_of_contract
               (c:ergoc_contract)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      let coname := c.(contract_name) in
      "class " ++ coname ++ " {" ++ eol
               ++ (javascript_of_clause_list c.(contract_clauses) coname eol quotel) ++ eol
               ++ "}" ++ eol.

    Definition preamble eol :=
      "" ++ "'use strict';" ++ eol
         ++ "/*eslint-disable no-unused-vars*/" ++ eol
         ++ "/*eslint-disable no-undef*/" ++ eol
         ++ "/*eslint-disable no-var*/" ++ eol
         ++ eol.

    Definition postamble eol :=
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
        | EType _ =>  ("","",t)
        | EExpr e => javascript_of_expression e t i eol quotel
        | EGlobal v e => javascript_of_global v e t i eol quotel
        | EImport _ => ("","",t)
        | EFunc f =>
          (javascript_function_of_ergo_func f None eol quotel,"null",t)
        | EContract c =>
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

    Definition dispatch_preamble
               (coname:string)
               (request:string)
               (response:string)
               (eol:string)
               (quotel:string) :=
      "/**" ++ eol
      ++ " * Execute the smart clause" ++ eol
      ++ " * @param {Context} context - the Accord context" ++ eol
      ++ " * @param {" ++ request ++ "} context.request - the incoming request" ++ eol
      ++ " * @param {" ++ response ++ "} context.response - the response" ++ eol
      ++ " * @AccordClauseLogic" ++ eol
      ++ " */" ++ eol
      ++ "function __dispatch(context) { return new " ++ coname ++ "().dispatch(context); }" ++ eol ++ eol.

    Definition javascript_of_package
               (p:ergoc_package)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      (preamble eol) ++ eol
                     ++ (javascript_of_declarations p.(package_declarations) 0 0 eol quotel)
                     ++ (postamble eol).

    Definition javascript_of_package_with_dispatch
               (coname:string)
               (request:string)
               (response:string)
               (p:ergoc_package)
               (eol:string)
               (quotel:string) : ErgoCodeGen.ergoc_javascript :=
      (preamble eol) ++ eol
                     ++ (dispatch_preamble coname request response eol quotel) ++ eol
                     ++ (javascript_of_declarations p.(package_declarations) 0 0 eol quotel)
                     ++ (postamble eol).
    
    Definition javascript_of_package_top
               (p:ergoc_package) : ErgoCodeGen.ergoc_javascript :=
      javascript_of_package p ErgoCodeGen.ergoc_javascript_eol_newline ErgoCodeGen.ergoc_javascript_quotel_double.

    Definition javascript_of_package_with_dispatch_top
               (coname:string)
               (request:string)
               (response:string)
               (p:ergoc_package) : ErgoCodeGen.ergoc_javascript :=
      javascript_of_package_with_dispatch coname request response p ErgoCodeGen.ergoc_javascript_eol_newline ErgoCodeGen.ergoc_javascript_quotel_double.

  End translate.
End ErgoCalculustoJavaScript.

