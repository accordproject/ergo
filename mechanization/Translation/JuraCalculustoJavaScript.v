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
Require Import Qcert.Common.CommonRuntime.
Require Import Error.
Require Import JuraBase.
Require Import JuraCalculus.
Require Import Qcert.NNRC.NNRCRuntime.

Section JuraCalculustoJavaScript.
  Context {fruntime:foreign_runtime}.

  Definition lookup_error (coname:string) (clname:string) :=
    let msg := ("Clause " ++ clname ++ " in contract " ++ coname ++ " not found")%string in
    CompilationError msg.
    
  Definition lookup_clause_code_from_package
             (coname:string) (clname:string) (p:jurac_package) : jresult nnrc :=
    let clause := lookup_clause_from_package coname clname p in
    jresult_of_option (code_from_clause clause) (lookup_error coname clname).

  Section translate.
    (* Basic modules *)
    Require Import Qcert.Common.CommonSystem.
    Require Import Qcert.Utils.OptimizerLogger.
    Require Import Qcert.NNRC.NNRCRuntime.
    Require Import Qcert.Translation.NNRCtoJavaScript.
    Require Import Qcert.Compiler.Driver.CompLang.

    (* Foreign Datatypes Support *)
    Require Import Qcert.Translation.ForeignToJavaScript.

    (* Context *)
    Context {ft:foreign_type}.
    Context {bm:brand_model}.
    Context {ftyping: foreign_typing}.
    Context {nnrc_logger:optimizer_logger string nnrc}.
    Context {ftojs:foreign_to_javascript}.
    Context {ftjson:foreign_to_JSON}.

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
               (e:jurac_expr)                  (* expression to translate *)
               (t : nat)                       (* next available unused temporary *)
               (i : nat)                       (* indentation level *)
               (eol:string)                    (* Choice of end of line character *)
               (quotel:string)                 (* Choice of quote character *)
      : javascript
        * javascript
        * nat
      := nnrcToJSunshadow e t i eol quotel nil nil.

    (** Global variable *)
    Definition javascript_of_global
               (v:string)                      (* global variable name *)
               (bind:jurac_expr)               (* expression for the global variable to translate *)
               (t : nat)                       (* next available unused temporary *)
               (i : nat)                       (* indentation level *)
               (eol:string)                    (* Choice of end of line character *)
               (quotel:string)                 (* Choice of quote character *)
      : javascript
        * javascript
        * nat
      := 
        let '(s1, e1, t2) := nnrcToJS bind t i eol quotel nil in
        let v0 := "v" ++ v in
        (s1 ++ (indent i) ++ "var " ++ v0 ++ " = " ++ e1 ++ ";" ++ eol,
         v0,
         t2).

    (** Single method *)
    Definition javascript_method_of_body
               (e:jurac_expr)
               (fname:string)
               (eol:string)
               (quotel:string) : javascript :=
      let input_v := "context" in
      nnrcToJSMethod input_v e 1 eol quotel (input_v::nil) fname.

    (** Single method *)
    Definition javascript_function_of_body
               (e:jurac_expr)
               (fname:string)
               (eol:string)
               (quotel:string) : javascript :=
      let input_v := "context" in
      let init_indent := 0 in
      lift_nnrc_core
        (fun e => nnrcToJSFun input_v e init_indent eol quotel (input_v::nil) fname)
        (nnrc_to_nnrc_core e).

    Definition javascript_function_of_jura_clause
               (c:jurac_clause)
               (coname:option string)
               (eol:string)
               (quotel:string) : javascript :=
      let fname := function_name_of_contract_clause_name coname c.(clause_name) in
      javascript_function_of_body c.(clause_closure).(closure_body) fname eol quotel.
    
    Definition javascript_function_of_jura_func
               (f:jurac_func)
               (coname:option string)
               (eol:string)
               (quotel:string) : javascript :=
      let fname := function_name_of_contract_clause_name coname f.(func_name) in
      javascript_function_of_body f.(func_closure).(closure_body) fname eol quotel ++ eol.
    
    Definition javascript_method_of_jura_clause
               (c:jurac_clause)
               (eol:string)
               (quotel:string) : javascript :=
      let fname := c.(clause_name) in
      javascript_method_of_body c.(clause_closure).(closure_body) fname eol quotel.
    
    Definition javascript_method_of_jura_func
               (f:jurac_func)
               (eol:string)
               (quotel:string) : javascript :=
      let fname := f.(func_name) in
      javascript_method_of_body f.(func_closure).(closure_body) fname eol quotel.

    Definition javascript_of_declaration
               (d:jurac_declaration)
               (coname:string)
               (eol:string)
               (quotel:string) : javascript :=
      match d with
      | Clause c => javascript_method_of_jura_clause c eol quotel
      | Func f => javascript_method_of_jura_func f eol quotel
      end.

    Definition javascript_of_declaration_list
               (dl:list declaration)
               (coname:string)
               (eol:string)
               (quotel:string) : javascript :=
      multi_append eol (fun d => javascript_of_declaration d coname eol quotel) dl.

    Definition javascript_of_contract
               (c:jurac_contract)
               (eol:string)
               (quotel:string) : javascript :=
      let coname := c.(contract_name) in
      "class " ++ coname ++ " {" ++ eol
               ++ (javascript_of_declaration_list c.(contract_declarations) coname eol quotel) ++ eol
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
    
    Definition javascript_of_statement
               (s : jurac_stmt)              (* statement to translate *)
               (t : nat)                     (* next available unused temporary *)
               (i : nat)                     (* indentation level *)
               (eol : string)
               (quotel : string)
      : javascript                           (* JavaScript statements for computing result *)
        * javascript                         (* JavaScript expression holding result *)
        * nat                                (* next available unused temporary *)
      :=
        match s with
        | JExpr e => javascript_of_expression e t i eol quotel
        | JGlobal v e => javascript_of_global v e t i eol quotel
        | JImport _ => ("","",t)
        | JFunc f =>
          (javascript_function_of_jura_func f None eol quotel,"null",t)
        | JContract c =>
          (javascript_of_contract c eol quotel,"null",t)
        end.

    Definition javascript_of_statements
               (sl : list jurac_stmt)        (* statements to translate *)
               (t : nat)                     (* next available unused temporary *)
               (i : nat)                     (* indentation level *)
               (eol : string)
               (quotel : string)
      : javascript
      := let proc_one (s:jurac_stmt) (acc:javascript * nat) : javascript * nat :=
             let '(s0, t0) := acc in
             let '(s1, e1, t1) := javascript_of_statement s t0 i eol quotel in
             (s0 ++ s1,
              t1) (* XXX Ignores e1! *)
         in
         let '(sn, tn) := fold_right proc_one ("",t) sl in
         sn.

    Definition dispatch_preamble (pname:string) (cname:string) (eol:string) (quotel:string) :=
      "/**" ++ eol
      ++ " * Execute the smart clause" ++ eol
      ++ " * @param {Context} context - the Accord context" ++ eol
      ++ " * @param {org.accordproject.latedeliveryandpenalty." ++ cname ++ "Request} context.request - the incoming request" ++ eol
      ++ " * @param {org.accordproject.latedeliveryandpenalty." ++ cname ++ "Response} context.response - the response" ++ eol
      ++ " * @AccordClauseLogic" ++ eol
      ++ " */" ++ eol
      ++ "function execute(context) {" ++ eol
      ++ "" ++ eol
      ++ "}".

    Definition find_class (sl:list jurac_stmt) :=
      "test".
    
    Definition javascript_dispatch (p:jurac_package) (eol:string) (quotel:string) : javascript :=
      let pname := p.(package_name) in
      let cname := find_class p.(package_statements) in
      dispatch_preamble pname "test" eol quotel.

    Definition javascript_of_package (p:jurac_package) (eol:string) (quotel:string) : javascript :=
      (preamble eol) ++ eol
                     ++ (javascript_of_statements p.(package_statements) 0 0 eol quotel)
                     (* ++ (javascript_dispatch p eol quotel) *)
                     ++ (postamble eol).

    Definition javascript_of_package_with_dispatch (p:jurac_package) (eol:string) (quotel:string) : javascript :=
      (preamble eol) ++ eol
                     ++ (javascript_of_statements p.(package_statements) 0 0 eol quotel)
                     (* ++ (javascript_dispatch p eol quotel) *)
                     ++ (postamble eol).

    Definition javascript_of_package_top (p:jurac_package) : javascript :=
      javascript_of_package p eol_newline quotel_double.

    Definition javascript_of_package_with_dispatch_top (p:jurac_package) : javascript :=
      javascript_of_package_with_dispatch p eol_newline quotel_double.

    Definition javascript_of_clause_code_in_package
               (coname:string) (clname:string) (p:jurac_package) : jresult javascript :=
      let expr_opt := lookup_clause_code_from_package coname clname p in
      jlift (fun e =>
               let fname := function_name_of_contract_clause_name (Some coname) clname in
               javascript_function_of_body e fname eol_newline quotel_double) expr_opt.

  End translate.
End JuraCalculustoJavaScript.

