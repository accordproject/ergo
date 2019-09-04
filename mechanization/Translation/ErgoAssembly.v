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

(** Ergo is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import List.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoAssembly.
  Definition toTextClause (prov:provenance) (template:laergo_expr) : laergo_clause :=
    mkClause
      prov
      "toText"%string
      (mkErgoTypeSignature
         prov
         nil
         (Some (ErgoTypeString prov))
         None)
      (Some (SReturn prov template)).

  Fixpoint add_template_to_clauses (prov:provenance) (template:laergo_expr) (cl:list laergo_clause) :=
    match cl with
    | nil =>
      (toTextClause prov template) :: nil
    | cl1 :: rest =>
      if (string_dec cl1.(clause_name) "toText")
      then cl
      else cl1 :: (add_template_to_clauses prov template rest)
    end.

  Definition add_template_to_contract (template:laergo_expr) (c:laergo_contract) :=
    mkContract
      c.(contract_annot)
      c.(contract_template)
      c.(contract_state)
      (add_template_to_clauses c.(contract_annot) template c.(contract_clauses)).

  Definition add_template_to_declaration (template:laergo_expr) (decl:laergo_declaration) :=
    match decl with
    | DContract a ln c => DContract a ln (add_template_to_contract template c)
    | _ => decl
    end.

  Definition add_template_to_module (template:laergo_expr) (main:laergo_module) :=
    mkModule
      main.(module_annot)
      main.(module_file)
      main.(module_prefix)              
      main.(module_namespace)
      (List.map (add_template_to_declaration template) main.(module_declarations)).

  Definition template_of_ergo_declaration (decl:laergo_declaration) : list (string * string) :=
    match decl with
    | DType prov tdecl =>
      let name := tdecl.(type_declaration_name) in
      match tdecl.(type_declaration_type) with
      | ErgoTypeAsset _ (Some tname) _ =>
        (name, tname)::nil
      | _ => nil
      end
    | _ => nil
    end.

  Definition template_of_ergo_declarations (decls:list laergo_declaration) : list (string * string) :=
    concat (map template_of_ergo_declaration decls).

  Definition template_of_ergo_module (emod:laergo_module) : list (string * string) :=
    template_of_ergo_declarations emod.(module_declarations).

  Definition template_of_ergo_modules (emods:list laergo_module) : list (string * string) :=
    concat (map template_of_ergo_module emods).

  Definition find_template prov (emods:list laergo_module) : eresult laergo_type :=
    let decls := template_of_ergo_modules emods in
    let templates :=
        filter
          (fun x =>
             let '(template, rel) := x in
             if string_dec rel "org.accordproject.cicero.contract.AccordContract"
             then true
             else if string_dec rel "org.accordproject.cicero.contract.AccordClause"
             then true
             else false) decls
    in
    match templates with
    | nil => template_type_not_found_error prov
    | (name,_) :: nil => esuccess (ErgoTypeClassRef prov name) nil
    | _ :: _ => more_than_one_template_type_error prov (String.concat "," (map fst templates))
    end.

  Definition empty_main (prov:provenance) (fname:string) (emods:list laergo_module) : eresult laergo_module :=
    elift (fun template =>
             mkModule prov fname "logic" "Empty"%string
                      (DContract prov "Ergo"%string
                                 (mkContract prov template None nil) :: nil))
          (find_template prov emods).

End ErgoAssembly.

