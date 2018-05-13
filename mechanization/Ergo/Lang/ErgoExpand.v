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
Require Import Qcert.Utils.ListAdd. (* For zip *)
Require Import Qcert.Compiler.Driver.CompLang.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoExpand.
  (* Context *)
  Definition create_call
             (cname:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (callparams:list (string * cto_type)) : eresult ergo_stmt :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => efailure (CompilationError "Parameter mismatch during main creation")
    | Some _ =>
      esuccess (SCallClause cname (EVar v0 :: effparamrest))
    end.

  Definition case_of_sig
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (s:signature) : eresult (match_case * ergo_stmt) :=
    let (cname, callparams) := s in
    match callparams with
    | nil => efailure (CompilationError ("Cannot create main if not at least one parameter in "++cname))
    | (param0, CTOClassRef type0)::otherparams =>
      elift (fun x =>
               let type0 := absolute_ref_of_relative_ref namespace type0 in
               ((Some v0,CaseType type0),x))
            (create_call cname v0 effparam0 effparamrest callparams)
    | (param0, _)::otherparams =>
      efailure (CompilationError ("Cannot create main for non-class type "++cname))
    end.

  Definition match_of_sigs
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (ss:list signature) : eresult ergo_stmt :=
    elift (fun s =>
             SMatch effparam0
                     s
                     (SThrow
                        (ENew (mkClassRef None "Error"%string)
                              (("message"%string, EConst (ErgoData.dstring ""))::nil))))
          (emaplift (case_of_sig namespace v0 effparam0 effparamrest) ss).

  Definition match_of_sigs_top
             (namespace:string)
             (effparams:list ergo_expr)
             (ss:list signature) :=
    match effparams with
    | nil => efailure (CompilationError ("Cannot create main if not at least one effective parameter"))
    | effparam0 :: effparamrest =>
      let v0 := ("$"++clause_main_name)%string in (** XXX To be worked on *)
      match_of_sigs namespace v0 effparam0 effparamrest ss
    end.

  Definition create_main_clause_for_contract (namespace:string) (c:ergo_contract) : eresult ergo_clause :=
    let sigs := lookup_contract_signatures c in
    let effparams := EVar "request"%string :: nil in
    elift
      (fun disp =>
         (mkClause clause_main_name
                   (mkLambda
                      (("request"%string,(CTOClassRef "Request"))::nil)
                      (CTOClassRef "Response")
                      None
                      disp)))
      (match_of_sigs_top namespace effparams sigs).

  Definition add_main_clause_to_contract (namespace:string) (c:ergo_contract) : eresult ergo_contract :=
    if in_dec string_dec clause_main_name
              (map (fun cl => cl.(clause_name)) c.(contract_clauses))
    then esuccess c
    else
      elift
        (fun main_clause =>
           mkContract
             c.(contract_name)
             c.(contract_template)
             (c.(contract_clauses) ++ (main_clause::nil)))
        (create_main_clause_for_contract namespace c).
  
  Definition add_main_clause_to_declaration (namespace:string) (d:ergo_declaration) : eresult declaration :=
    match d with
    | EType td => esuccess (EType td)
    | EExpr e => esuccess (EExpr e)
    | EGlobal v e => esuccess (EGlobal v e)
    | EImport id => esuccess (EImport id)
    | EFunc fd => esuccess (EFunc fd)
    | EContract cd =>
      elift EContract (add_main_clause_to_contract namespace cd)
    end.
    
  
  Definition add_main_clauses_to_declarations
             (namespace:string) (dl:list ergo_declaration) : eresult (list ergo_declaration) :=
    emaplift (add_main_clause_to_declaration namespace) dl.
    
  Definition add_main_clauses_to_package (p:ergo_package) : eresult ergo_package :=
    elift
      (mkPackage
         p.(package_namespace))
      (add_main_clauses_to_declarations p.(package_namespace) p.(package_declarations)).

  (** Pre-processing. At the moment only add main clauses when missing *)
  Definition ergo_package_expand (p:ergo_package) : eresult ergo_package :=
    add_main_clauses_to_package p.
  
End ErgoExpand.

