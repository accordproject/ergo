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

Section ErgoNNRCtoJava.
  Local Open Scope string_scope.

  Definition function_name_of_contract_clause_name (coname:option string) (clname:string) : string :=
    match coname with
    | None => clname
    | Some coname => coname ++ "_" ++ clname
    end.

  (** Global expression *)
  Definition java_of_expression
             (e:nnrc_expr)                  (* expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.java
      * ErgoCodeGen.java_data
      * nat
    := ErgoCodeGen.nnrc_expr_java_unshadow e t i eol quotel nil nil.

  (** Global variable *)
  Definition java_of_global
             (v:string)                      (* global variable name *)
             (bind:nnrc_expr)               (* expression for the global variable to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol:string)                    (* Choice of end of line character *)
             (quotel:string)                 (* Choice of quote character *)
    : ErgoCodeGen.java
      * ErgoCodeGen.java_data
      * nat
    := 
      let '(s1, e1, t2) := ErgoCodeGen.nnrc_expr_to_java bind t i eol quotel nil in
      let v0 := "v" ++ v in
      (s1 ++ (ErgoCodeGen.java_indent i) ++ "var " ++ v0 ++ " = " ++ (ErgoCodeGen.from_java_data e1) ++ ";" ++ eol,
       ErgoCodeGen.mk_java_data v0,
       t2).

  (** Single method *)
  Definition java_method_of_body
             (e:nnrc_expr)
             (fname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.java :=
    let input_v := "context" in
    ErgoCodeGen.nnrc_expr_to_java_method input_v e 1 eol quotel ((input_v, input_v)::nil) fname.

  Definition java_method_of_ergo_clause
             (c:nnrc_function)
             (eol:string)
             (quotel:string) : ErgoCodeGen.java :=
    let fname := c.(functionn_name) in
    java_method_of_body c.(functionn_lambda).(lambdan_body) fname eol quotel.
    
  Definition java_of_clause_list
             (cl:list nnrc_function)
             (coname:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.java :=
    multi_append eol (fun c => java_method_of_ergo_clause c eol quotel) cl.

  Definition java_of_contract
             (c:nnrc_contract)
             (eol:string)
             (quotel:string) : ErgoCodeGen.java :=
    let coname := c.(contractn_name) in
    "class " ++ coname ++ " {" ++ eol
             ++ (java_of_clause_list c.(contractn_clauses) coname eol quotel) ++ eol
             ++ "}" ++ eol.

  Definition preamble (eol:string) := eol.

  Definition postamble (eol:string) := eol.
    
  Definition java_of_declaration
             (s : nnrc_declaration)       (* statement to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.java               (* Java statements for computing result *)
      * ErgoCodeGen.java_data              (* Java expression holding result *)
      * nat                                (* next available unused temporary *)
    :=
      match s with
      | ENExpr e => java_of_expression e t i eol quotel
      | ENGlobal v e => java_of_global v e t i eol quotel
      | ENFunc f => ("",ErgoCodeGen.mk_java_data "",t) (* XXX Not sure what to do with functions *)
      | ENContract c =>
        (java_of_contract c eol quotel,ErgoCodeGen.mk_java_data "null",t)
      end.

  Definition java_of_declarations
             (sl : list nnrc_declaration) (* statements to translate *)
             (t : nat)                     (* next available unused temporary *)
             (i : nat)                     (* indentation level *)
             (eol : string)
             (quotel : string)
    : ErgoCodeGen.java
    := let proc_one
             (s:nnrc_declaration)
             (acc:ErgoCodeGen.java * nat) : ErgoCodeGen.java * nat :=
           let '(s0, t0) := acc in
           let '(s1, e1, t1) := java_of_declaration s t0 i eol quotel in
           (s0 ++ s1,
            t1) (* XXX Ignores e1! *)
       in
       let '(sn, tn) := fold_right proc_one ("",t) sl in
       sn.

  Definition nnrc_package_to_java
             (p:nnrc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.java :=
    (preamble eol) ++ eol
                   ++ (java_of_declarations p.(packagen_declarations) 0 0 eol quotel)
                   ++ (postamble eol).

  Definition nnrc_package_to_java_top
             (p:nnrc_package) : ErgoCodeGen.java :=
    nnrc_package_to_java p ErgoCodeGen.java_eol_newline ErgoCodeGen.java_quotel_double.

End ErgoNNRCtoJava.

