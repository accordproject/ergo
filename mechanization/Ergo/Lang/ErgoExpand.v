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
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Ast.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoExpand.
  (* Context *)

  Definition create_call
             (prov:provenance)
             (cname:string)
             (v0:string)
             (effparam0:laergo_expr)
             (effparamrest:list laergo_expr)
             (callparams:list (string * laergo_type)) : eresult laergo_stmt :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => main_parameter_mismatch_error prov
    | Some _ =>
      esuccess (SCallClause prov (EThisContract prov) cname (EVar prov v0 :: effparamrest))
    end.

  Definition case_of_sig
             (prov:provenance)
             (v0:string)
             (effparam0:laergo_expr)
             (effparamrest:list laergo_expr)
             (s: (string * laergo_type_signature)) : eresult (ergo_pattern * laergo_stmt) :=
    let cname := (fst s) in
    let callparams := (snd s).(type_signature_params) in
    match callparams with
    | nil => main_at_least_one_parameter_error prov
    | (param0, et)::otherparams =>
      match et with
      | ErgoTypeClassRef _ type0 =>
        elift (fun x =>
                 (CaseLet prov v0 (Some type0),x))
              (create_call prov cname v0 effparam0 effparamrest callparams)
      | _ => main_not_a_class_error prov cname
      end
    end.

  Definition match_of_sigs
             (prov:provenance)
             (v0:string)
             (effparam0:laergo_expr)
             (effparamrest:list laergo_expr)
             (ss:list (string * laergo_type_signature)) : eresult laergo_stmt :=
    elift (fun s =>
             SMatch prov effparam0
                    s
                    (SThrow prov
                            (EConst prov (default_match_error_content prov ""))))
          (emaplift (case_of_sig prov v0 effparam0 effparamrest) ss).

  Definition match_of_sigs_top
             (prov:provenance)
             (effparams:list ergo_expr)
             (ss:list (string * laergo_type_signature)) :=
    match effparams with
    | nil => main_at_least_one_parameter_error prov
    | effparam0 :: effparamrest =>
      let v0 := ("$"++clause_main_name)%string in (** XXX To be worked on *)
      match_of_sigs prov v0 effparam0 effparamrest ss
    end.

  Definition filter_init (sigs:list (string * laergo_type_signature)) :=
    filter (fun s =>
              if (string_dec (fst s) clause_init_name)
              then false
              else true) sigs.

  Definition create_main_clause_for_contract
             (prov:provenance)
             (c:laergo_contract) : eresult laergo_clause :=
    let sigs := lookup_contract_signatures c in
    let sigs := filter_init sigs in
    let effparams := EVar prov "request"%string :: nil in
    elift
      (fun disp =>
         (mkClause prov
                   clause_main_name
                   (mkErgoTypeSignature
                      prov
                      (("request"%string,ErgoTypeClassRef prov default_request_absolute_name)::nil)
                      (Some (ErgoTypeClassRef prov default_response_absolute_name))
                      None
                      None)
                   (Some disp)))
      (match_of_sigs_top prov effparams sigs).

  (* XXX Has to be fixed to use brands -- needs fixes in code-generation *)
  Definition default_state (prov:provenance) : laergo_expr :=
    EUnaryOp prov
             (OpBrand (default_state_absolute_name::nil))
             (EConst prov (drec (("stateId",dstring "1") :: nil)))%string.

  Definition create_init_clause_for_contract
             (prov:provenance)
             (c:laergo_contract) : laergo_clause :=
    let effparams : list laergo_expr := EVar prov "request"%string :: nil in
    let init_body :=
        SSetState prov (default_state prov)
                  (SReturn prov (EConst prov dunit))
    in
    mkClause prov
             clause_init_name
             (mkErgoTypeSignature
                prov
                (("request"%string, ErgoTypeClassRef prov default_request_absolute_name)::nil)
                (Some (ErgoTypeUnit prov))
                None
                (Some (ErgoTypeClassRef prov default_emits_absolute_name)))
             (Some init_body).

  Definition add_init_clause_to_contract (c:laergo_contract) : laergo_contract :=
    let prov := c.(contract_annot) in
    if in_dec string_dec clause_init_name
              (map (fun cl => cl.(clause_name)) c.(contract_clauses))
    then c
    else
      let init_clause :=
          create_init_clause_for_contract prov c
      in
      mkContract
        prov
        c.(contract_template)
        c.(contract_state)
        (c.(contract_clauses) ++ (init_clause::nil)).

  Definition add_main_clause_to_contract (c:laergo_contract) : eresult laergo_contract :=
    let prov := c.(contract_annot) in
    if in_dec string_dec clause_main_name
              (map (fun cl => cl.(clause_name)) c.(contract_clauses))
    then esuccess c
    else
      elift
        (fun main_clause =>
           mkContract
             prov
             c.(contract_template)
             c.(contract_state)
             (c.(contract_clauses) ++ (main_clause::nil)))
        (create_main_clause_for_contract prov c).
  
  Definition ergo_expand_declaration
             (d:laergo_declaration) : eresult laergo_declaration :=
    match d with
    | DNamespace _ _ => esuccess d
    | DImport _ _ => esuccess d
    | DType _ _ => esuccess d
    | DStmt _ _ => esuccess d
    | DConstant _ _ _ _ => esuccess d
    | DFunc _ _ _ => esuccess d
    | DContract _ cn c =>
      let cd := add_init_clause_to_contract c in
      elift
        (fun dd =>
           (DContract (decl_annot d) cn dd))
        (add_main_clause_to_contract cd)
    | DSetContract _ _ _ => esuccess d
    end.
    
  Definition ergo_expand_declarations
             (dl:list laergo_declaration) : eresult (list laergo_declaration) :=
    emaplift ergo_expand_declaration dl.
    
  (** Pre-processing. At the moment only add main clauses when missing *)
  Definition ergo_expand_module (p:laergo_module) : eresult laergo_module :=
    elift
      (fun ds => mkModule
                   p.(module_annot)
                   p.(module_file)
                   p.(module_namespace)
                   ds)
      (ergo_expand_declarations p.(module_declarations)).

  Definition ergo_expand_modules (pl:list laergo_module) : eresult (list laergo_module) :=
    emaplift (ergo_expand_module) pl.

End ErgoExpand.

