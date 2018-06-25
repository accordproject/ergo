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
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoExpand.
  (* Context *)

  Definition create_call
             (loc:location)
             (cname:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (callparams:list (string * ergo_type)) : eresult ergo_stmt :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => main_parameter_mismatch_error loc
    | Some _ =>
      esuccess (mk_stmt loc (SCallClause cname (mk_expr loc (EVar v0) :: effparamrest)))
    end.

  Definition case_of_sig
             (loc:location)
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (s:ergo_type_signature) : eresult (ergo_pattern * ergo_stmt) :=
    let cname := s.(type_signature_name) in
    let callparams := s.(type_signature_params) in
    match callparams with
    | nil => main_at_least_one_parameter_error loc
    | (param0, et)::otherparams =>
      match type_desc et with
      | ErgoTypeClassRef type0 =>
        elift (fun x =>
                 let type0 := absolute_name_of_name_ref namespace type0 in
                 (CaseLet v0 (Some type0),x))
              (create_call loc cname v0 effparam0 effparamrest callparams)
      | _ => main_not_a_class_error loc cname
      end
    end.

  Definition match_of_sigs
             (loc:location)
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (ss:list ergo_type_signature) : eresult ergo_stmt :=
    elift (fun s =>
             mk_stmt loc
                     (SMatch effparam0
                             s
                             (mk_stmt loc
                                      (SThrow
                                         (mk_expr loc (ENew (RelativeRef None "Error"%string)
                                                            (("message"%string, mk_expr loc (EConst (ErgoData.dstring "")))::nil)))))))
          (emaplift (case_of_sig loc namespace v0 effparam0 effparamrest) ss).

  Definition match_of_sigs_top
             (loc:location)
             (namespace:string)
             (effparams:list ergo_expr)
             (ss:list ergo_type_signature) :=
    match effparams with
    | nil => main_at_least_one_parameter_error loc
    | effparam0 :: effparamrest =>
      let v0 := ("$"++clause_main_name)%string in (** XXX To be worked on *)
      match_of_sigs loc namespace v0 effparam0 effparamrest ss
    end.

  Definition filter_init sigs :=
    filter (fun s =>
              if (string_dec s.(type_signature_name) clause_init_name)
              then false
              else true) sigs.
  
  Definition create_main_clause_for_contract
             (loc:location)
             (namespace:string)
             (c:ergo_contract) : eresult ergo_clause :=
    let sigs := lookup_contract_signatures c in
    let sigs := filter_init sigs in
    let effparams := mk_expr loc (EVar "request"%string) :: nil in
    elift
      (fun disp =>
         (mkClause clause_main_name
                   loc
                   (mkLambda
                      (("request"%string,mk_type loc (ErgoTypeClassRef default_request_type))::nil)
                      (mk_type loc (ErgoTypeClassRef default_response_type))
                      None
                      None
                      disp)))
      (match_of_sigs_top loc namespace effparams sigs).

  (* XXX Has to be fixed to use brands -- needs fixes in code-generation *)
  Definition default_state (loc:location) : ergo_expr :=
    mk_expr loc
            (EConst
               (drec (("$class",dstring default_state_name)
                        :: ("stateId",dstring "1")
                        :: nil)))%string.
  Definition default_response (loc:location) : ergo_expr :=
    mk_expr loc
            (EConst
               (drec (("$class",dstring default_response_name)
                        :: nil)))%string.
  
  Definition create_init_clause_for_contract
             (loc:location)
             (namespace:string)
             (c:ergo_contract) : ergo_clause :=
    let effparams := mk_expr loc (EVar "request"%string) :: nil in
    let init_body :=
        mk_stmt loc
                (SSetState (default_state loc)
                           (mk_stmt loc (SReturn (default_response loc))))
    in
    mkClause clause_init_name
             loc
             (mkLambda
                (("request"%string,mk_type loc (ErgoTypeClassRef default_request_type))::nil)
                (mk_type loc ErgoTypeNone)
                None
                (Some (mk_type loc (ErgoTypeClassRef default_emits_type)))
                init_body).

  Definition add_init_clause_to_contract (namespace:string) (c:ergo_contract) : ergo_contract :=
    let loc := c.(contract_location) in
    if in_dec string_dec clause_init_name
              (map (fun cl => cl.(clause_name)) c.(contract_clauses))
    then c
    else
      let init_clause :=
          create_init_clause_for_contract loc namespace c
      in
      mkContract
        c.(contract_name)
        loc
        c.(contract_template)
        c.(contract_state)
        (c.(contract_clauses) ++ (init_clause::nil)).

  Definition add_main_clause_to_contract (namespace:string) (c:ergo_contract) : eresult ergo_contract :=
    let loc := c.(contract_location) in
    if in_dec string_dec clause_main_name
              (map (fun cl => cl.(clause_name)) c.(contract_clauses))
    then esuccess c
    else
      elift
        (fun main_clause =>
           mkContract
             c.(contract_name)
             loc
             c.(contract_template)
             c.(contract_state)
             (c.(contract_clauses) ++ (main_clause::nil)))
        (create_main_clause_for_contract loc namespace c).
  
  Definition add_main_init_clause_to_declaration
             (namespace:string)
             (d:ergo_declaration) : eresult ergo_declaration :=
    match decl_desc d with
    | DType _ => esuccess d
    | DStmt _ => esuccess d
    | DConstant _ _ => esuccess d
    | DFunc _ => esuccess d
    | DContract c =>
      let cd := add_init_clause_to_contract namespace c in
      elift
        (fun dd =>
           mk_decl (decl_loc d) (DContract dd))
        (add_main_clause_to_contract namespace cd)
    end.
    
  Definition add_main_init_clauses_to_declarations
             (namespace:string) (dl:list ergo_declaration) : eresult (list ergo_declaration) :=
    emaplift (add_main_init_clause_to_declaration namespace) dl.
    
  Definition add_main_init_clauses_to_module (p:ergo_module) : eresult ergo_module :=
    elift
      (fun ds => mkModule
                   p.(module_namespace)
                   p.(module_location)
                   p.(module_imports)
                   ds)
      (add_main_init_clauses_to_declarations p.(module_namespace) p.(module_declarations)).

  (** Pre-processing. At the moment only add main clauses when missing *)
  Definition ergo_module_expand (p:ergo_module) : eresult ergo_module :=
    add_main_init_clauses_to_module p.
  
End ErgoExpand.

