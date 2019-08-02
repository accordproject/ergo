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

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Types.ErgoTypetoErgoCType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCSugar.

Section ErgoCExpand.
  Context {m : brand_model}.

  Definition create_call
             (prov:provenance)
             (coname:string)
             (clname:string)
             (v0:string)
             (effparam0:ergoc_expr)
             (effparamrest:list ergoc_expr)
             (callparams:list (string * laergo_type)) : eresult ergoc_expr :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => main_parameter_mismatch_error prov
    | Some _ =>
      esuccess (ECallClause prov coname clname (EVar prov v0 :: effparamrest)) nil
    end.

  Definition case_of_sig
             (prov:provenance)
             (coname:string)
             (v0:string)
             (effparam0:ergoc_expr)
             (effparamrest:list ergoc_expr)
             (s: (string * sigc)) : eresult (list (absolute_name * (ergo_pattern * ergoc_expr))) :=
    let clname := (fst s) in
    let callparams := (snd s).(sigc_params) in
    match callparams with
    | nil => main_at_least_one_parameter_error prov
    | this_contract::this_state::this_emit::(param0, et)::otherparams =>
      match et with
      | ErgoTypeClassRef _ type0 =>
        let prunedcallparams := (param0, et)::otherparams in
        elift (fun x =>
                 ((type0,(CaseLet prov v0 (Some type0),x))::nil))
              (create_call prov coname clname v0 effparam0 effparamrest prunedcallparams)
      | _ => esuccess nil nil (* XXX May want to make this a warning *)
      end
    | _ => esuccess nil nil (* XXX May want to make this a warning *)
    end.

  Definition make_cases
             (order:list laergo_type_declaration)
             (prov:provenance)
             (xy:list (absolute_name * (laergo_pattern * ergoc_expr)))
    : eresult (list (laergo_pattern * ergoc_expr)) :=
    let oxy := sort_given_topo_order order fst xy in
    duplicate_clause_for_request_check prov (map fst oxy) (map snd oxy).

  Definition match_of_sigs
             (order:list laergo_type_declaration)
             (prov:provenance)
             (coname:string)
             (v0:string)
             (effparam0:ergoc_expr)
             (effparamrest:list ergoc_expr)
             (ss:list (string * sigc)) : eresult ergoc_expr :=
    eolift (fun (xy:list (absolute_name * (ergo_pattern * ergoc_expr))) =>
              let ecases := make_cases order prov xy in
              elift (fun cases =>
                       EMatch prov effparam0
                              cases
                              (EFailure prov
                                        (EConst prov (default_match_error_content prov))))
                    ecases)
           (eflatmaplift (case_of_sig prov coname v0 effparam0 effparamrest) ss).

  Definition match_of_sigs_top
             (order:list laergo_type_declaration)
             (prov:provenance)
             (coname:string)
             (effparams:list ergoc_expr)
             (ss:list (string * sigc)) :=
    match effparams with
    | nil => main_at_least_one_parameter_error prov
    | effparam0 :: effparamrest =>
      let v0 := ("$"++clause_main_name)%string in (** XXX To be worked on *)
      match_of_sigs order prov coname v0 effparam0 effparamrest ss
    end.

  Definition filter_init (sigs:list (string * sigc)) :=
    filter (fun s =>
              if (string_dec (fst s) clause_init_name)
              then false
              else true) sigs.

  Definition create_main_clause_for_contract
             (order:list laergo_type_declaration)
             (prov:provenance)
             (coname:string)
             (c:ergoc_contract) : eresult (local_name * ergoc_function) :=
    let sigs := lookup_contractc_request_signatures c in
    let sigs := filter_init sigs in
    let effparams := EVar prov "request"%string :: nil in
    let template := c.(contractc_template) in
    let params := (("request"%string, ErgoTypeClassRef prov default_request_absolute_name)::nil) in
    let state := c.(contractc_state) in
    elift
      (EClauseAsFunction
         prov
         clause_main_name
         template
         None (* Emit type *)
         state
         None (* Response type *)
         params)
      (elift Some (match_of_sigs_top order prov coname effparams sigs)).

  (* XXX Has to be fixed to use brands -- needs fixes in code-generation *)
  Definition default_state (prov:provenance) : ergoc_expr :=
    EUnaryBuiltin prov
             (OpBrand (default_state_absolute_name::nil))
             (EConst prov (drec (("stateId",dstring (default_state_absolute_name ++ "#1")) :: nil)))%string.

  Definition create_init_clause_for_contract
             (prov:provenance)
             (c:ergoc_contract) : local_name * ergoc_function :=
    let template := c.(contractc_template) in
    let state := c.(contractc_state) in
    let params := nil in
    let init_body :=
        setState prov (default_state prov)
                 (EReturn prov (EConst prov dunit))
    in
    EClauseAsFunction
      prov
      clause_init_name
      template
      None (* Emit type *)
      state
      None (* Response type *)
      params
      (Some init_body).

  Definition add_init_clause_to_contract (c:ergoc_contract) : ergoc_contract :=
    let prov := c.(contractc_annot) in
    if in_dec string_dec clause_init_name (map fst c.(contractc_clauses))
    then c
    else
      let init_clause := create_init_clause_for_contract prov c
      in
      mkContractC
        prov
        c.(contractc_template)
        c.(contractc_state)
        (c.(contractc_clauses) ++ (init_clause::nil)).

  Definition add_main_clause_to_contract
             (order:list laergo_type_declaration)
             (coname:string)
             (c:ergoc_contract) : eresult ergoc_contract :=
    let prov := c.(contractc_annot) in
    if in_dec string_dec clause_main_name (map fst c.(contractc_clauses))
    then esuccess c nil
    else
      elift
        (fun main_clause =>
           mkContractC
             prov
             c.(contractc_template)
             c.(contractc_state)
             (c.(contractc_clauses) ++ (main_clause::nil)))
        (create_main_clause_for_contract order prov coname c).
  
  Definition ergoc_expand_declaration
             (order:list laergo_type_declaration)
             (d:ergoc_declaration) : eresult ergoc_declaration :=
    match d with
    | DCExpr _ _ => esuccess d nil
    | DCConstant _ _ _ _ => esuccess d nil
    | DCFunc _ _ _ => esuccess d nil
    | DCContract prov cn c =>
      let cd := add_init_clause_to_contract c in
      elift
        (fun dd =>
           (DCContract prov cn dd))
        (add_main_clause_to_contract order cn cd)
    end.
    
  Definition ergoc_expand_declarations
             (order:list laergo_type_declaration)
             (dl:list ergoc_declaration) : eresult (list ergoc_declaration) :=
    emaplift (ergoc_expand_declaration order) dl.

  (** Pre-processing. At the moment only add main clauses when missing *)
  Definition ergoc_expand_module
             (order:list laergo_type_declaration)
             (p:ergoc_module) : eresult ergoc_module :=
    elift
      (fun ds => mkModuleC
                   p.(modulec_annot)
                   p.(modulec_namespace)
                   ds)
      (ergoc_expand_declarations order p.(modulec_declarations)).

End ErgoCExpand.

