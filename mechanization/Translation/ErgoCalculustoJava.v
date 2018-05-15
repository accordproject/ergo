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
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculustoJava.
  Local Open Scope string_scope.

  Definition function_name_of_contract_clause_name (coname:option string) (clname:string) : string :=
    match coname with
    | None => clname
    | Some coname => coname ++ "_" ++ clname
    end.

  (** Global expression *)
  Definition java_of_expression
             (e:ergoc_expr)                  (* expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.ergoc_java
      * ErgoCodeGen.java_data
      * nat
    := ErgoCodeGen.ergoc_expr_java_unshadow e t i eol quotel nil nil.

  (** Global variable *)
  Definition java_of_global
             (v:string)                      (* global variable name *)
             (bind:ergoc_expr)               (* expression for the global variable to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.ergoc_java
      * ErgoCodeGen.java_data
      * nat
    := 
      let '(s1, e1, t2) := ErgoCodeGen.ergoc_expr_to_java bind t i eol quotel nil in
      let v0 := "v" ++ v in
      (s1 ++ (ErgoCodeGen.ergoc_java_indent i) ++ "var " ++ v0 ++ " = " ++ (ErgoCodeGen.from_java_data e1) ++ ";" ++ eol,
       ErgoCodeGen.mk_java_data v0,
       t2).

  (** Single method *)
  Definition java_method_of_body
             (e:ergoc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_java :=
    let input_v := "context" in
    ErgoCodeGen.ergoc_expr_to_java_method input_v e 1 eol quotel ((input_v, input_v)::nil) fname.

  Definition java_method_of_ergo_clause
             (c:ergoc_clause)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_java :=
    let fname := c.(clause_name) in
    java_method_of_body c.(clause_lambda).(lambda_body) fname eol quotel.
    
  Definition java_of_clause_list
             (cl:list clause)
             (coname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_java :=
    multi_append eol (fun c => java_method_of_ergo_clause c eol quotel) cl.

  Definition java_of_contract
             (c:ergoc_contract)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_java :=
    let coname := c.(contract_name) in
    "class " ++ coname ++ " {" ++ eol
             ++ (java_of_clause_list c.(contract_clauses) coname eol quotel) ++ eol
             ++ "}" ++ eol.

  Definition preamble (eol:string) := eol.

  Definition postamble (eol:string) := eol.
    
  Definition java_of_declaration
             (s : ergoc_declaration)       (* statement to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.ergoc_java               (* Java statements for computing result *)
      * ErgoCodeGen.java_data              (* Java expression holding result *)
      * nat                                (* next available unused temporary *)
    :=
      match s with
      | EType _ =>  ("",ErgoCodeGen.mk_java_data "",t)
      | EExpr e => java_of_expression e t i eol quotel
      | EGlobal v e => java_of_global v e t i eol quotel
      | EImport _ => ("",ErgoCodeGen.mk_java_data "",t)
      | EFunc f => ("",ErgoCodeGen.mk_java_data "",t) (* XXX Not sure what to do with functions *)
      | EContract c =>
        (java_of_contract c eol quotel,ErgoCodeGen.mk_java_data "null",t)
      end.

  Definition java_of_declarations
             (sl : list ergoc_declaration) (* statements to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.ergoc_java
    := let proc_one
             (s:ergoc_declaration)
             (acc:ErgoCodeGen.ergoc_java * nat) : ErgoCodeGen.ergoc_java * nat :=
           let '(s0, t0) := acc in
           let '(s1, e1, t1) := java_of_declaration s t0 i eol quotel in
           (s0 ++ s1,
            t1) (* XXX Ignores e1! *)
       in
       let '(sn, tn) := fold_right proc_one ("",t) sl in
       sn.

  Definition ergoc_package_to_java
             (p:ergoc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_java :=
    (preamble eol) ++ eol
                   ++ (java_of_declarations p.(package_declarations) 0 0 eol quotel)
                   ++ (postamble eol).

  Definition ergoc_package_to_java_top
             (p:ergoc_package) : ErgoCodeGen.ergoc_java :=
    ergoc_package_to_java p ErgoCodeGen.ergoc_java_eol_newline ErgoCodeGen.ergoc_java_quotel_double.

End ErgoCalculustoJava.

