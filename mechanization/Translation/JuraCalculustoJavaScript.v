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

  Section lookup_clause.
    (** Returns clause code *)
    Definition lookup_from_clause (clname:string) (c:jurac_clause) : option jurac_clause :=
      if (string_dec clname c.(clause_name))
      then Some c
      else None.

    Definition lookup_from_func (clname:string) (c:jurac_func) : option jurac_func :=
      if (string_dec clname c.(func_name))
      then Some c
      else None.

    Definition code_from_clause (c:option jurac_clause) : option nnrc :=
      match c with
      | None => None
      | Some c => Some c.(clause_closure).(closure_body)
      end.
    
    Definition code_from_func (f:option jurac_func) : option nnrc :=
      match f with
      | None => None
      | Some f => Some f.(func_closure).(closure_body)
      end.
    
    Definition lookup_code_from_clause (clname:string) (c:jurac_clause) : option nnrc :=
      code_from_clause (lookup_from_clause clname c).

    Definition lookup_code_from_func (clname:string) (c:jurac_func) : option nnrc :=
      code_from_func (lookup_from_func clname c).

    Definition lookup_clause_from_declaration (clname:string) (d:jurac_declaration) : option jurac_clause :=
      match d with
      | Clause c => lookup_from_clause clname c
      | Func f => None
      end.

    Definition lookup_clause_from_declarations (clname:string) (dl:list jurac_declaration) : option jurac_clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_clause_from_declaration clname d
           end
        ) dl None.
    
    Definition lookup_contract_from_contract (coname:string) (c:jurac_contract) : option jurac_contract :=
      if (string_dec coname c.(contract_name))
      then Some c
      else None.

    Definition lookup_clause_from_contract
               (coname:string) (clname:string) (c:jurac_contract) : option jurac_clause :=
      match lookup_contract_from_contract coname c with
      | None => None
      | Some c =>
        lookup_clause_from_declarations clname c.(contract_declarations)
      end.

    Definition lookup_clause_from_statement (coname:string) (clname:string) (d:jurac_stmt) : option jurac_clause :=
      match d with
      | JContract c => lookup_clause_from_contract coname clname c
      | _ => None
      end.

    Definition lookup_clause_from_statements
               (coname:string) (clname:string) (sl:list jurac_stmt) : option jurac_clause :=
      List.fold_left
        (fun acc d =>
           match acc with
           | Some e => Some e
           | None => lookup_clause_from_statement coname clname d
           end
        ) sl None.
    
    Definition lookup_clause_from_package
               (coname:string) (clname:string) (p:jurac_package) : option jurac_clause :=
      lookup_clause_from_statements coname clname p.(package_statements).

    Definition lookup_error (coname:string) (clname:string) :=
      let msg := ("Clause " ++ clname ++ " in contract " ++ coname ++ " not found")%string in
      CompilationError msg.
    
    Definition lookup_clause_code_from_package
               (coname:string) (clname:string) (p:jurac_package) : jresult nnrc :=
      let clause := lookup_clause_from_package coname clname p in
      jresult_of_option (code_from_clause clause) (lookup_error coname clname).
  End lookup_clause.

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

    Definition javascript_method_of_body
               (eol:string) (quotel:string) (fname:string) (e:jurac_expr) : javascript :=
      let input_v := "constants" in
      nnrcToJSMethod input_v e 1 eol quotel (input_v::nil) fname.

    Definition javascript_function_of_body (fname:string) (e:jurac_expr) : javascript :=
      lift_nnrc_core nnrc_to_js_top_with_name (nnrc_to_nnrc_core e) fname.

    Definition javascript_of_clause_code (fname:string) (e:jurac_expr) : javascript :=
      javascript_function_of_body fname e.

    Definition function_name_of_contract_clause_name (coname:string) (clname:string) : string :=
      coname ++ "_" ++ clname.

    Definition javascript_of_clause (eol:string) (quotel:string) (coname:string) (c:jurac_clause) : javascript :=
      let fname := function_name_of_contract_clause_name coname c.(clause_name) in
      javascript_method_of_body eol quotel fname c.(clause_closure).(closure_body).
    
    Definition javascript_of_func (eol:string) (quotel:string) (c:jurac_func) : javascript :=
      let fname := c.(func_name) in
      javascript_function_of_body fname c.(func_closure).(closure_body).
    
    Definition javascript_of_declaration (eol:string) (quotel:string) (coname:string) (d:jurac_declaration) : javascript :=
      match d with
      | Clause c => javascript_of_clause eol quotel coname c
      | Func f => javascript_of_func eol quotel f
      end.

    Definition multi_append {A} separator (f:A -> string) (elems:list A) : string :=
      match elems with
      | nil => ""
      | e :: elems' =>
        (fold_left (fun acc e => acc ++ separator ++ (f e)) elems' (f e))%string
      end.

    Definition javascript_of_declaration_list (eol:string) (quotel:string) (coname:string) (dl:list declaration) : javascript :=
      multi_append eol (javascript_of_declaration eol quotel coname) dl.

    Definition javascript_of_contract (eol:string) (quotel:string) (c:jurac_contract) : javascript :=
      let coname := c.(contract_name) in
      "class " ++ coname ++ " {" ++ eol
               ++ (javascript_of_declaration_list eol quotel coname c.(contract_declarations)) ++ eol
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
          (javascript_of_func eol quotel f ++ eol,"null",t)
        | JContract c =>
          (javascript_of_contract eol quotel c,"null",t)
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
    
    Definition javascript_of_package (eol:string) (quotel:string) (c:jurac_package) : javascript :=
      (preamble eol) ++ eol
                     ++ (javascript_of_statements c.(package_statements) 0 0 eol quotel)
                     ++ (postamble eol).

    Definition javascript_of_package_top (c:jurac_package) : javascript :=
      javascript_of_package eol_newline quotel_double c.

    Definition javascript_of_clause_code_in_package
               (coname:string) (clname:string) (p:jurac_package) : jresult javascript :=
      let expr_opt := lookup_clause_code_from_package coname clname p in
      jlift (fun e =>
               let fname := function_name_of_contract_clause_name coname clname in
               javascript_of_clause_code fname e) expr_opt.

  End translate.
End JuraCalculustoJavaScript.

