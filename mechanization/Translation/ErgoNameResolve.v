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
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Translation.CTOtoErgo.

Section ErgoNameResolution.

  Fixpoint namespace_ctxt_of_ergo_decls
           (ctxt:namespace_ctxt)
           (ns:namespace_name)
           (dls:list lrergo_declaration) : (namespace_name * namespace_ctxt) :=
    match dls with
    | nil => (ns, ctxt)
    | DNamespace _ ns' :: rest =>
      (ns', ctxt)
    | DImport _ _ :: rest =>
      namespace_ctxt_of_ergo_decls ctxt ns rest
    | DType tname td :: rest =>
      let ln := td.(type_declaration_name) in
      let an := absolute_name_of_local_name ns ln in
      let ectxt := ctxt.(namespace_ctxt_enums) in
      let ctxt :=
          if type_declaration_is_enum td.(type_declaration_type)
          then update_namespace_context_enums ctxt (an::ectxt)
          else ctxt
      in
      let (ns, ctxt) := namespace_ctxt_of_ergo_decls ctxt ns rest in
      (ns, add_type_to_namespace_ctxt ctxt ns ln an)
    | DStmt _ _ :: rest =>
      let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
      ctxt
    | DConstant _ ln ta cd :: rest =>
      let an := absolute_name_of_local_name ns ln in
      let (ns, ctxt) := namespace_ctxt_of_ergo_decls ctxt ns rest in
      (ns, add_constant_to_namespace_ctxt ctxt ns ln an)
    | DFunc _ ln fd :: rest =>
      let an := absolute_name_of_local_name ns ln in
      let (ns, ctxt) := namespace_ctxt_of_ergo_decls ctxt ns rest in
      (ns, add_function_to_namespace_ctxt ctxt ns ln an)
    | DContract _ ln _ :: rest =>
      let an := absolute_name_of_local_name ns ln in
      let (ns, ctxt) := namespace_ctxt_of_ergo_decls ctxt ns rest in
      (ns, add_contract_to_namespace_ctxt ctxt ns ln an)
    | DSetContract _ ln _ :: rest =>
      namespace_ctxt_of_ergo_decls ctxt ns rest
    end.

  Definition namespace_ctxt_of_ergo_module (ctxt:namespace_ctxt) (m:lrergo_module) : namespace_ctxt :=
    snd (namespace_ctxt_of_ergo_decls ctxt m.(module_namespace) m.(module_declarations)).

  Definition namespace_ctxt_of_ergo_modules (ctxt:namespace_ctxt) (ml:list lrergo_module) : namespace_ctxt :=
    fold_left namespace_ctxt_of_ergo_module ml ctxt.

  Definition namespace_ctxt_of_cto_packages (ctxt:namespace_ctxt) (ctos:list cto_package) : namespace_ctxt :=
    let mls := map cto_package_to_ergo_module ctos in
    fold_left namespace_ctxt_of_ergo_module mls ctxt.

  Section ResolveImports.
    (** This applies imports *)
    Definition lookup_one_import
               (ctxt:namespace_ctxt)
               (ic:limport_decl) : eresult namespace_table :=
      match ic with
      | ImportAll prov ns =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl => esuccess tbl nil
        | None => import_not_found_error prov ns
        end
      | ImportSelf prov ns =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl => esuccess tbl nil
        | None => esuccess empty_namespace_table nil
        end
      | ImportName prov ns ln =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl =>
          match lookup string_dec tbl.(namespace_table_types) ln with
          | None => import_name_not_found_error prov ns ln
          | Some an => esuccess (one_type_to_namespace_table ln an) nil
          end
        | None => import_not_found_error prov ns
        end
      end.

    Definition resolve_one_import
               (ctxt:namespace_ctxt)
               (ic:limport_decl) : eresult namespace_ctxt :=
      elift (fun tbl =>
               mkNamespaceCtxt
                 ctxt.(namespace_ctxt_modules)
                 ctxt.(namespace_ctxt_namespace)
                 ctxt.(namespace_ctxt_current_module) (* Only update in-scope for modules *)
                 (namespace_table_app ctxt.(namespace_ctxt_current_in_scope) tbl)
                 ctxt.(namespace_ctxt_enums)
                 ctxt.(namespace_ctxt_abstract))
            (lookup_one_import ctxt ic).

    (* Stdlib modules imported automatically *)
    Definition builtin_imports :=
      accordproject_base_namespace
        :: accordproject_stdlib_namespace
        :: nil.
    Definition is_builtin_import (ns:namespace_name) : bool :=
      if in_dec string_dec ns builtin_imports
      then true
      else false.

    (* All Stdlib modules, including those not imported automatically *)
    Definition stdlib_imports :=
      accordproject_base_namespace
        :: accordproject_stdlib_namespace
        :: accordproject_time_namespace
        :: nil.
    Definition is_stdlib_import (ns:namespace_name) : bool :=
      if in_dec string_dec ns stdlib_imports
      then true
      else false.

  End ResolveImports.

  Section NameResolution.
    (** Name resolution for type declarations *)
    Fixpoint resolve_ergo_type
             (ectxt: enum_ctxt)
             (nsctxt:namespace_ctxt)
             (t:lrergo_type) : eresult laergo_type :=
      match t with
      | ErgoTypeAny prov => esuccess (ErgoTypeAny prov) nil
      | ErgoTypeNothing prov => esuccess (ErgoTypeNothing prov) nil
      | ErgoTypeUnit prov => esuccess (ErgoTypeUnit prov) nil
      | ErgoTypeBoolean prov => esuccess (ErgoTypeBoolean prov) nil
      | ErgoTypeString prov => esuccess (ErgoTypeString prov) nil
      | ErgoTypeDouble prov => esuccess (ErgoTypeDouble prov) nil
      | ErgoTypeLong prov => esuccess (ErgoTypeLong prov) nil
      | ErgoTypeInteger prov => esuccess (ErgoTypeInteger prov) nil
      | ErgoTypeDateTime prov => esuccess (ErgoTypeDateTime prov) nil
      | ErgoTypeDuration prov => esuccess (ErgoTypeDuration prov) nil
      | ErgoTypePeriod prov => esuccess (ErgoTypePeriod prov) nil
      | ErgoTypeClassRef prov rn =>
        let an := resolve_type_name prov nsctxt rn in
        elift (fun an =>
                 if in_dec string_dec an ectxt (* XXX Enums are uninterpreted, i.e., treated as String *)
                 then ErgoTypeString prov
                 else ErgoTypeClassRef prov an)
              an
      | ErgoTypeOption prov t =>
        elift (ErgoTypeOption prov) (resolve_ergo_type ectxt nsctxt t)
      | ErgoTypeRecord prov r =>
        let initial_map := map (fun xy => (fst xy, resolve_ergo_type ectxt nsctxt (snd xy))) r in
        let lifted_map := emaplift (fun xy => elift (fun t => (fst xy, t)) (snd xy)) initial_map in
        elift (ErgoTypeRecord prov) lifted_map
      | ErgoTypeArray prov t =>
        elift (ErgoTypeArray prov) (resolve_ergo_type ectxt nsctxt t)
      | ErgoTypeSum prov t1 t2 =>
        elift2 (ErgoTypeSum prov)
               (resolve_ergo_type ectxt nsctxt t1)
               (resolve_ergo_type ectxt nsctxt t2)
      end.

    Definition resolve_ergo_type_struct
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (t:list (string * lrergo_type)) : eresult (list (string * laergo_type)) :=
      emaplift (fun xy =>
                  elift (fun t => (fst xy, t)) (resolve_ergo_type ectxt nsctxt (snd xy))) t.

    Definition resolve_type_annotation
               (prov:provenance)
               (nsctxt:namespace_ctxt)
               (en:option relative_name) : eresult (option absolute_name) :=
      match en with
      | None => esuccess None nil
      | Some rn => elift Some (resolve_type_name prov nsctxt rn)
      end.

    Definition resolve_extends
               (prov:provenance)
               (nsctxt:namespace_ctxt)
               (en:rextends) : eresult aextends :=
      resolve_type_annotation prov nsctxt en.

    Definition resolve_ergo_type_signature
               (prov:provenance)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (fname:string)
               (sig:lrergo_type_signature) : eresult laergo_type_signature :=
      let params_types := resolve_ergo_type_struct ectxt nsctxt (sig.(type_signature_params)) in
      let params_types :=
          eolift (fun ps => (duplicate_function_params_check prov fname (map fst ps) ps)) params_types
      in
      let output_type : eresult (option laergo_type) :=
          match sig.(type_signature_output) with
          | None => esuccess None nil
          | Some out_ty =>
            elift Some (resolve_ergo_type ectxt nsctxt out_ty)
          end
      in
      let emits_type : eresult (option laergo_type) :=
          match sig.(type_signature_emits) with
          | None => esuccess None nil
          | Some emits_ty =>
            elift Some (resolve_ergo_type ectxt nsctxt emits_ty)
          end
      in
      elift3 (mkErgoTypeSignature
                sig.(type_signature_annot))
             params_types
             output_type
             emits_type.

    Definition resolve_ergo_type_clauses
               (prov:provenance)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (cls:list (string * lrergo_type_signature)) : eresult (list (string * laergo_type_signature)) :=
      emaplift (fun xy => elift (fun r => (fst xy, r))
                                (resolve_ergo_type_signature prov ectxt nsctxt (fst xy) (snd xy))) cls.

    Definition resolve_ergo_type_declaration_desc
               (prov:provenance)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (name:string)
               (d:lrergo_type_declaration_desc)
      : eresult laergo_type_declaration_desc :=
      match d with
      | ErgoTypeEnum l => esuccess (ErgoTypeEnum l) nil
      | ErgoTypeTransaction isabs extends_name ergo_type_struct =>
        elift2 (ErgoTypeTransaction isabs)
               (resolve_extends prov nsctxt extends_name)
               (resolve_ergo_type_struct ectxt nsctxt ergo_type_struct)
      | ErgoTypeConcept isabs extends_name ergo_type_struct =>
        elift2 (ErgoTypeConcept isabs)
               (resolve_extends prov nsctxt extends_name)
               (resolve_ergo_type_struct ectxt nsctxt ergo_type_struct)
      | ErgoTypeEvent isabs extends_name ergo_type_struct =>
        elift2 (ErgoTypeEvent isabs)
               (resolve_extends prov nsctxt extends_name)
               (resolve_ergo_type_struct ectxt nsctxt ergo_type_struct)
      | ErgoTypeAsset isabs extends_name ergo_type_struct =>
        elift2 (ErgoTypeAsset isabs)
               (resolve_extends prov nsctxt extends_name)
               (resolve_ergo_type_struct ectxt nsctxt ergo_type_struct)
      | ErgoTypeParticipant isabs extends_name ergo_type_struct =>
        elift2 (ErgoTypeParticipant isabs)
               (resolve_extends prov nsctxt extends_name)
               (resolve_ergo_type_struct ectxt nsctxt ergo_type_struct)
      | ErgoTypeGlobal ergo_type =>
        elift ErgoTypeGlobal (resolve_ergo_type ectxt nsctxt ergo_type)
      | ErgoTypeFunction ergo_type_signature =>
        elift ErgoTypeFunction
              (resolve_ergo_type_signature prov ectxt nsctxt name ergo_type_signature)
      | ErgoTypeContract template_type state_type clauses_sigs =>
        elift3 ErgoTypeContract
               (resolve_ergo_type ectxt nsctxt template_type)
               (resolve_ergo_type ectxt nsctxt state_type)
               (resolve_ergo_type_clauses prov ectxt nsctxt clauses_sigs)
      end.
 
    Definition resolve_ergo_type_declaration
               (module_ns:namespace_name)
               (nsctxt:namespace_ctxt)
               (decl: enum_ctxt * abstract_ctxt * lrergo_type_declaration)
      : eresult (enum_ctxt * abstract_ctxt * laergo_type_declaration) :=
      let '(ectxt,actxt,decl) := decl in
      let name := absolute_name_of_local_name module_ns decl.(type_declaration_name) in
      let ectxt :=
          if type_declaration_is_enum decl.(type_declaration_type)
          then name :: ectxt
          else ectxt
      in
      let actxt :=
          if type_declaration_is_abstract decl.(type_declaration_type)
          then name :: actxt
          else actxt
      in
      let edecl_desc :=
          resolve_ergo_type_declaration_desc
            decl.(type_declaration_annot) ectxt nsctxt decl.(type_declaration_name) decl.(type_declaration_type)
      in
      elift (fun k => (ectxt, actxt, mkErgoTypeDeclaration decl.(type_declaration_annot) name k)) edecl_desc.

    Definition resolve_ergo_pattern
               (nsctxt:namespace_ctxt)
               (p:lrergo_pattern) : eresult (laergo_pattern) :=
      match p with
      | CaseData prov d => esuccess (CaseData prov d) nil
      | CaseWildcard prov ta => elift (CaseWildcard prov) (resolve_type_annotation prov nsctxt ta)
      | CaseLet prov v ta => elift (CaseLet prov v) (resolve_type_annotation prov nsctxt ta)
      | CaseLetOption prov v ta => elift (CaseLetOption prov v) (resolve_type_annotation prov nsctxt ta)
      end.
    
    (** Name resolution for expressions *)
    Fixpoint resolve_ergo_expr
             (ectxt: enum_ctxt)
             (nsctxt:namespace_ctxt)
             (e:lrergo_expr) : eresult laergo_expr :=
      match e with
      | EThisContract prov => esuccess (EThisContract prov) nil
      | EThisClause prov => esuccess (EThisClause prov) nil
      | EThisState prov => esuccess (EThisState prov) nil
      | EVar prov v => esuccess (EVar prov v) nil
      | EConst prov d => esuccess (EConst prov d) nil
      | ENone prov => esuccess (ENone prov) nil
      | ESome prov e =>
        elift (ESome prov)
              (resolve_ergo_expr ectxt nsctxt e)
      | EArray prov el =>
        let init_el := esuccess nil nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr ectxt nsctxt e)
              acc
        in
        elift (EArray prov) (fold_right proc_one init_el el)
      | EUnaryOperator prov u e =>
        elift (EUnaryOperator prov u)
              (resolve_ergo_expr ectxt nsctxt e)
      | EBinaryOperator prov b e1 e2 =>
        elift2 (EBinaryOperator prov b)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_expr ectxt nsctxt e2)
      | EUnaryBuiltin prov u e =>
        elift (EUnaryBuiltin prov u)
              (resolve_ergo_expr ectxt nsctxt e)
      | EBinaryBuiltin prov b e1 e2 =>
        elift2 (EBinaryBuiltin prov b)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_expr ectxt nsctxt e2)
      | EIf prov e1 e2 e3 =>
        elift3 (EIf prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_expr ectxt nsctxt e2)
               (resolve_ergo_expr ectxt nsctxt e3)
      | ELet prov v ta e1 e2 =>
        let rta :=
            match ta with
            | None => esuccess None nil
            | Some ta => elift Some (resolve_ergo_type ectxt nsctxt ta)
            end
        in
        elift3 (ELet prov v)
               rta
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_expr ectxt nsctxt e2)
      | EPrint prov e1 e2 =>
        elift2 (EPrint prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_expr ectxt nsctxt e2)
      | ENew prov cr el =>
        let rcr := resolve_type_name prov nsctxt cr in
        let init_rec := esuccess nil nil in
        let proc_one (att:string * lrergo_expr) (acc:eresult (list (string * laergo_expr))) :=
            let attname := fst att in
            let e := resolve_ergo_expr ectxt nsctxt (snd att) in
            elift2 (fun e => fun acc => (attname,e)::acc) e acc
        in
        elift2 (ENew prov) rcr (fold_right proc_one init_rec el)
      | ERecord prov el =>
        let init_rec := esuccess nil nil in
        let proc_one (att:string * lrergo_expr) (acc:eresult (list (string * laergo_expr))) :=
            let attname := fst att in
            let e := resolve_ergo_expr ectxt nsctxt (snd att) in
            elift2 (fun e => fun acc => (attname,e)::acc) e acc
        in
        elift (ERecord prov) (fold_right proc_one init_rec el)
      | ECallFun prov fname el =>
        let rfname := resolve_function_name prov nsctxt fname in
        let init_el := esuccess nil nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr ectxt nsctxt e)
              acc
        in
        elift2 (ECallFun prov) rfname (fold_right proc_one init_el el)
      | ECallFunInGroup prov gname fname el =>
        let rgname := resolve_contract_name prov nsctxt gname in
        let init_el := esuccess nil nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr ectxt nsctxt e)
              acc
        in
        elift3 (ECallFunInGroup prov) rgname (esuccess fname nil) (fold_right proc_one init_el el)
      | EMatch prov e0 ecases edefault =>
        let ec0 := resolve_ergo_expr ectxt nsctxt e0 in
        let eccases :=
            let proc_one acc (ecase : lrergo_pattern * lrergo_expr) :=
                let (pcase, pe) := ecase in
                let apcase := resolve_ergo_pattern nsctxt pcase in
                eolift (fun apcase =>
                          eolift
                            (fun acc =>
                               elift (fun x => (apcase, x)::acc)
                                     (resolve_ergo_expr ectxt nsctxt pe)) acc)
                       apcase
            in
            fold_left proc_one ecases (esuccess nil nil)
        in
        let ecdefault := resolve_ergo_expr ectxt nsctxt edefault in
        eolift
          (fun ec0 : laergo_expr =>
             eolift
               (fun eccases : list (laergo_pattern * laergo_expr) =>
                  elift
                    (fun ecdefault : laergo_expr =>
                    EMatch prov ec0 eccases ecdefault)
                    ecdefault) eccases) ec0
      | EForeach prov foreachs econd e2 =>
        let re2 := resolve_ergo_expr ectxt nsctxt e2 in
        let recond :=
            match econd with
            | None => esuccess None nil
            | Some econd => elift Some (resolve_ergo_expr ectxt nsctxt econd)
            end
        in
        let init_e := esuccess nil nil in
        let proc_one
              (foreach:string * lrergo_expr)
              (acc:eresult (list (string * laergo_expr)))
            : eresult (list (string * laergo_expr)) :=
            let v := fst foreach in
            let e := resolve_ergo_expr ectxt nsctxt (snd foreach) in
            elift2 (fun e => fun acc => (v,e)::acc)
                 e
                 acc
        in
        elift3 (EForeach prov)
               (fold_right proc_one init_e foreachs)
               recond
               re2
      end.

    (** Name resolution for statements *)
    Fixpoint resolve_ergo_stmt
             (ectxt: enum_ctxt)
             (nsctxt:namespace_ctxt)
             (e:lrergo_stmt) : eresult laergo_stmt :=
      match e with
      | SReturn prov e => elift (SReturn prov) (resolve_ergo_expr ectxt nsctxt e)
      | SFunReturn prov e => elift (SFunReturn prov) (resolve_ergo_expr ectxt nsctxt e)
      | SThrow prov e =>  elift (SThrow prov) (resolve_ergo_expr ectxt nsctxt e)
      | SCallClause prov e0 fname el =>
        let init_el := esuccess nil nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr ectxt nsctxt e)
              acc
        in
        elift3 (SCallClause prov)
               (resolve_ergo_expr ectxt nsctxt e0)
               (esuccess fname nil)
               (fold_right proc_one init_el el)
      | SCallContract prov e0 el =>
        let init_el := esuccess nil nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr ectxt nsctxt e)
              acc
        in
        elift2 (SCallContract prov)
               (resolve_ergo_expr ectxt nsctxt e0)
               (fold_right proc_one init_el el)
      | SSetState prov e1 s2 =>
        elift2 (SSetState prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_stmt ectxt nsctxt s2)
      | SEmit prov e1 s2 =>
        elift2 (SEmit prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_stmt ectxt nsctxt s2)
      | SLet prov v ta e1 s2 =>
        let rta :=
            match ta with
            | None => esuccess None nil
            | Some ta => elift Some (resolve_ergo_type ectxt nsctxt ta)
            end
        in
        elift3 (SLet prov v)
               rta
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_stmt ectxt nsctxt s2)
      | SPrint prov e1 s2 =>
        elift2 (SPrint prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_stmt ectxt nsctxt s2)
      | SIf prov e1 s2 s3 =>
        elift3 (SIf prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               (resolve_ergo_stmt ectxt nsctxt s2)
               (resolve_ergo_stmt ectxt nsctxt s3)
      | SEnforce prov e1 os2 s3 =>
        let rs2 :=
            match os2 with
            | None => esuccess None nil
            | Some s2 => elift Some (resolve_ergo_stmt ectxt nsctxt s2)
            end
        in
        elift3 (SEnforce prov)
               (resolve_ergo_expr ectxt nsctxt e1)
               rs2
               (resolve_ergo_stmt ectxt nsctxt s3)
      | SMatch prov e0 scases sdefault =>
        let ec0 := resolve_ergo_expr ectxt nsctxt e0 in
        let sccases :=
            let proc_one acc (scase : lrergo_pattern * lrergo_stmt) :=
                let (pcase, pe) := scase in
                let apcase := resolve_ergo_pattern nsctxt pcase in
                eolift (fun apcase =>
                          eolift
                            (fun acc =>
                               elift (fun x => (apcase, x)::acc)
                                     (resolve_ergo_stmt ectxt nsctxt pe)) acc)
                       apcase
            in
            fold_left proc_one scases (esuccess nil nil)
        in
        let scdefault := resolve_ergo_stmt ectxt nsctxt sdefault in
        eolift
          (fun ec0 : laergo_expr =>
             eolift
               (fun sccases : list (laergo_pattern * laergo_stmt) =>
                  elift
                    (fun scdefault : laergo_stmt =>
                    SMatch prov ec0 sccases scdefault)
                    scdefault) sccases) ec0
      end.

    (** Name resolution for lambdas *)

    Definition resolve_ergo_function
               (module_ns:namespace_name)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (name:string)
               (f:lrergo_function) : eresult laergo_function :=
      let prov := f.(function_annot) in
      let rbody :=
          match f.(function_body) with
          | None => esuccess None nil
          | Some body => elift Some (resolve_ergo_expr ectxt nsctxt body)
          end
      in
      elift2 (mkFunc prov)
             (resolve_ergo_type_signature prov ectxt nsctxt name f.(function_sig))
             rbody.
    
    Definition resolve_ergo_clause
               (module_ns:namespace_name)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (c:ergo_clause) : eresult laergo_clause :=
      let prov := c.(clause_annot) in
      let rcname := c.(clause_name) in
      let rbody :=
          match c.(clause_body) with
          | None => esuccess None nil
          | Some body => elift Some (resolve_ergo_stmt ectxt nsctxt body)
          end
      in
      elift2 (mkClause prov rcname)
             (resolve_ergo_type_signature prov ectxt nsctxt rcname c.(clause_sig))
             rbody.

    Definition resolve_ergo_clauses
               (module_ns:namespace_name)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (cl:list ergo_clause) : eresult (list laergo_clause) :=
      emaplift (resolve_ergo_clause module_ns ectxt nsctxt) cl.

    Definition resolve_ergo_contract
               (module_ns:namespace_name)
               (ectxt: enum_ctxt)
               (nsctxt:namespace_ctxt)
               (c:lrergo_contract) : eresult laergo_contract :=
      let prov := c.(contract_annot) in
      let rtemplate := resolve_ergo_type ectxt nsctxt c.(contract_template) in
      let rstate :=
          match c.(contract_state) with
          | None => esuccess None nil
          | Some state => elift Some (resolve_ergo_type ectxt nsctxt state)
          end
      in
      elift3 (mkContract prov)
             rtemplate
             rstate
             (resolve_ergo_clauses module_ns ectxt nsctxt c.(contract_clauses)).

    Definition resolve_ergo_declaration
               (nsctxt:namespace_ctxt)
               (d:lrergo_declaration)
      : eresult (laergo_declaration * namespace_ctxt) :=
      let module_ns : namespace_name := nsctxt.(namespace_ctxt_namespace) in
      let ectxt := nsctxt.(namespace_ctxt_enums) in
      let actxt := nsctxt.(namespace_ctxt_abstract) in
      match d with
      | DNamespace prov ns =>
        esuccess (DNamespace prov ns, local_namespace_scope nsctxt ns) nil
      | DImport prov id =>
        elift (fun x => (DImport prov id, x)) (resolve_one_import nsctxt id)
      | DType prov td =>
        let ln := td.(type_declaration_name) in
        let an := absolute_name_of_local_name module_ns ln in
        let nsctxt := add_type_to_namespace_ctxt_current nsctxt ln an in
        elift (fun xy : enum_ctxt * abstract_ctxt * laergo_type_declaration =>
                 let '(ectxt,actxt,x) := xy in
                 let nsctxt := update_namespace_context_enums nsctxt ectxt in
                 let nsctxt := update_namespace_context_abstract nsctxt actxt in
                 (DType prov x, nsctxt))
              (resolve_ergo_type_declaration module_ns nsctxt (ectxt, actxt, td))
      | DStmt prov st =>
        elift (fun x => (DStmt prov x, nsctxt)) (resolve_ergo_stmt ectxt nsctxt st)
      | DConstant prov ln ta e =>
        let an := absolute_name_of_local_name module_ns ln in
        let rta :=
            match ta with
            | None => esuccess None nil
            | Some ta => elift Some (resolve_ergo_type ectxt nsctxt ta)
            end
        in
        let nsctxt := add_constant_to_namespace_ctxt_current nsctxt ln an in
        elift2 (fun ta x => (DConstant prov ln ta x, nsctxt))
               rta
               (resolve_ergo_expr ectxt nsctxt e)
      | DFunc prov ln fd =>
        let an := absolute_name_of_local_name module_ns ln in
        let nsctxt := add_function_to_namespace_ctxt_current nsctxt ln an in
        elift (fun x => (DFunc prov an x, nsctxt)) (resolve_ergo_function module_ns ectxt nsctxt an fd)
      | DContract prov ln c  =>
        let an := absolute_name_of_local_name module_ns ln in
        let nsctxt := add_contract_to_namespace_ctxt_current nsctxt ln an in
        elift (fun x => (DContract prov an x, nsctxt)) (resolve_ergo_contract module_ns ectxt nsctxt c)
      | DSetContract prov rn e1  =>
        eolift (fun an =>
                  elift (fun x => (DSetContract prov an x, nsctxt))
                        (resolve_ergo_expr ectxt nsctxt e1))
               (resolve_contract_name prov nsctxt rn)
      end.

    Definition resolve_ergo_declarations
               (ctxt:namespace_ctxt)
               (decls: list lrergo_declaration)
      : eresult (list ergo_declaration * namespace_ctxt) :=
      elift_context_fold_left
        resolve_ergo_declaration
        decls
        ctxt.

    Definition silently_resolve_ergo_declarations
               (ctxt:namespace_ctxt)
               (decls: list lrergo_declaration)
      : eresult namespace_ctxt :=
      elift snd (resolve_ergo_declarations ctxt decls).

  End NameResolution.

  Section Top.
    Definition init_namespace_ctxt : namespace_ctxt :=
      empty_namespace_ctxt no_namespace.

    Definition patch_cto_imports
               (ctxt_ns:namespace_name)
               (decls: list lrergo_declaration) : list lrergo_declaration :=
      if is_builtin_import ctxt_ns
      then (DImport dummy_provenance (ImportSelf dummy_provenance ctxt_ns)) :: decls
      else
        (* Add built-in modules to import, first.
           Make sure to add current namespace to the list of imports - i.e., import self. *)
        (DImport dummy_provenance (ImportAll dummy_provenance accordproject_base_namespace))
          :: (DImport dummy_provenance (ImportSelf dummy_provenance ctxt_ns))
          :: decls.

    (* Resolve imports for Ergo *)
    Definition patch_ergo_imports
               (ctxt_ns:namespace_name)
               (decls: list lrergo_declaration) : list lrergo_declaration :=
      if is_builtin_import ctxt_ns
      then app decls (DImport dummy_provenance (ImportSelf dummy_provenance ctxt_ns) :: nil)
      else
        (* Add built-in modules to import, first.
           Make sure to add current namespace to the list of imports - i.e., import self. *)
        (DImport dummy_provenance (ImportAll dummy_provenance accordproject_base_namespace))
          ::(DImport dummy_provenance (ImportAll dummy_provenance accordproject_stdlib_namespace))
          ::(DImport dummy_provenance (ImportSelf dummy_provenance ctxt_ns))
          :: decls.
      
    (* New namespace *)
    Definition new_cto_package_namespace
               (ctxt:namespace_ctxt)
               (ns:namespace_name)
               (m:lrergo_module)
      : eresult namespace_ctxt :=
      if is_builtin_import ns
      then esuccess ctxt nil
      else
        let builtin_cto_imports :=
            (DImport dummy_provenance (ImportAll dummy_provenance accordproject_base_namespace))
              :: (DImport dummy_provenance (ImportSelf dummy_provenance ns))
              :: nil
        in
        let ctxt := new_namespace_scope ctxt ns in
        let ctxt := namespace_ctxt_of_ergo_module ctxt m in (* XXX Pre-populate namespace for CTO modules to handle not-yet-declared names *)
        silently_resolve_ergo_declarations ctxt builtin_cto_imports.

    Definition new_ergo_module_namespace
               (ctxt:namespace_ctxt)
               (ns:namespace_name)
      : eresult namespace_ctxt :=
      if is_builtin_import ns
      then esuccess ctxt nil
      else
        let builtin_cto_imports :=
            (DImport dummy_provenance (ImportAll dummy_provenance accordproject_base_namespace))
              ::(DImport dummy_provenance (ImportAll dummy_provenance accordproject_stdlib_namespace))
              ::(DImport dummy_provenance (ImportSelf dummy_provenance ns))
              :: nil
        in
        let ctxt := new_namespace_scope ctxt ns in
        silently_resolve_ergo_declarations ctxt builtin_cto_imports.

    (* Resolve a CTO package *)
    Definition resolve_cto_package
               (ctxt:namespace_ctxt)
               (cto:lrcto_package) : eresult (laergo_module * namespace_ctxt) :=
      let m := cto_package_to_ergo_module cto in
      let module_ns := m.(module_namespace) in
      let ctxt := new_namespace_scope ctxt module_ns in
      let ctxt := namespace_ctxt_of_ergo_module ctxt m in (* XXX Pre-populate namespace for CTO modules to handle not-yet-declared names *)
      let declarations := m.(module_declarations) in
      let ctxt_ns := ctxt.(namespace_ctxt_namespace) in
      elift
        (fun nc =>
           (mkModule
              m.(module_annot)
              m.(module_file)
              m.(module_prefix)
              module_ns
              (fst nc), snd nc))
        (resolve_ergo_declarations
           ctxt
           (patch_cto_imports module_ns declarations)).

    Definition resolve_ergo_module
               (ctxt:namespace_ctxt)
               (m:lrergo_module) : eresult (laergo_module * namespace_ctxt) :=
      let module_ns := m.(module_namespace) in
      let ctxt := new_namespace_scope ctxt module_ns in
      let declarations := m.(module_declarations) in
      let ctxt_ns := ctxt.(namespace_ctxt_namespace) in
      elift
        (fun nc =>
           (mkModule
              m.(module_annot)
              m.(module_file)
              m.(module_prefix)
              module_ns
              (fst nc), snd nc))
        (resolve_ergo_declarations
           ctxt
           (patch_ergo_imports module_ns declarations)).

    Definition resolve_ergo_modules
               (ctxt:namespace_ctxt)
               (ml:list lrergo_module) : eresult (list laergo_module * namespace_ctxt) :=
      elift_context_fold_left
        resolve_ergo_module
        ml
        ctxt.

    Definition resolve_cto_packages
               (ctxt:namespace_ctxt)
               (ctos:list lrcto_package) : eresult (list laergo_module * namespace_ctxt) :=
      let ctxt := namespace_ctxt_of_cto_packages ctxt ctos in (* XXX Pre-populate namespace for CTO modules to handle not-yet-declared names *)
      elift_context_fold_left
        resolve_cto_package
        ctos
        ctxt.

    Fixpoint split_ctos_and_ergos (inputs:list lrergo_input)
      : (list lrcto_package * list lrergo_module * option lrergo_module) :=
      match inputs with
      | nil => (nil, nil, None)
      | InputCTO cto :: rest =>
        let '(ctos', rest', p') := split_ctos_and_ergos rest in
        (cto :: ctos', rest', p')
      | InputErgo ml :: rest =>
        let '(ctos', rest', p') := split_ctos_and_ergos rest in
        match p' with
        | None =>
          if is_stdlib_import ml.(module_namespace)
          then (ctos', ml :: rest', None)
          else (ctos', rest', Some ml)
        | Some _ => (ctos', ml :: rest', p')
        end
      end.

  End Top.

  Section Examples.
    Local Open Scope string.
    Definition ergo_typed1 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_provenance
        "c1"
        (ErgoTypeConcept
           false
           None
           (("a", ErgoTypeBoolean dummy_provenance)
              ::("b", (ErgoTypeClassRef dummy_provenance (None, "c3")))::nil)).

    Definition ergo_typed2 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_provenance
        "c2"
        (ErgoTypeConcept
           false
           None
           (("c", ErgoTypeBoolean dummy_provenance)
              ::("d", (ErgoTypeClassRef dummy_provenance (None, "c1")))::nil)).

    Definition ergo_funcd1 : lrergo_function :=
      mkFunc
        dummy_provenance
        (mkErgoTypeSignature
           dummy_provenance
           nil
           (Some (ErgoTypeBoolean dummy_provenance))
           None)
        None.
    
    Definition ergo_funcd2 : lrergo_function :=
      mkFunc
        dummy_provenance
        (mkErgoTypeSignature
           dummy_provenance
           nil
           (Some (ErgoTypeBoolean dummy_provenance))
           None)
        (Some (ECallFun dummy_provenance (None,"addFee") nil)).

    Definition ergo_clause2 : lrergo_clause :=
      mkClause
        dummy_provenance
        "addFee2"
        (mkErgoTypeSignature
           dummy_provenance
           nil
           (Some (ErgoTypeBoolean dummy_provenance))
           None)
        (Some (SReturn dummy_provenance (ECallFun dummy_provenance (None,"addFee") nil))).

    Definition ergo_contractd1 : lrergo_contract :=
      mkContract
        dummy_provenance
        (ErgoTypeBoolean dummy_provenance)
        None
        (ergo_clause2::nil).
    
    Definition ergo_module1 : lrergo_module :=
      mkModule
        dummy_provenance
        ""
        ""
        "n1"
        (DImport dummy_provenance (ImportAll dummy_provenance "n2")
        ::DFunc dummy_provenance "addFee" ergo_funcd1
        ::DContract dummy_provenance "MyContract" ergo_contractd1
        ::DType dummy_provenance ergo_typed1
        ::DType dummy_provenance ergo_typed2::nil).
    
    Definition ergo_typed3 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_provenance
        "c3"
        (ErgoTypeConcept
           false
           None
           (("a", ErgoTypeBoolean dummy_provenance)
              ::("b", ErgoTypeString dummy_provenance)::nil)).

    Definition ergo_typed_top : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_provenance
        "top"
        (ErgoTypeGlobal
           (ErgoTypeAny dummy_provenance)).

    Definition ergo_module2 : lrergo_module :=
      mkModule
        dummy_provenance "" "" "n2" (DType dummy_provenance ergo_typed3::nil).

    Definition ergo_hl : lrergo_module :=
      mkModule
        dummy_provenance "" "" accordproject_base_namespace (DType dummy_provenance ergo_typed_top::nil).

    Definition ergo_stdlib : lrergo_module :=
      mkModule
        dummy_provenance "" "" accordproject_stdlib_namespace (DType dummy_provenance ergo_typed_top::nil).

    Definition ml1 : list lrergo_module := ergo_hl :: ergo_stdlib :: ergo_module2 :: ergo_module1 :: nil.
    Definition aml1 := resolve_ergo_modules (empty_namespace_ctxt "TEST") ml1.
    (* Eval vm_compute in aml1. *)

    Definition ml2 : list lrergo_module := ergo_hl :: ergo_stdlib :: ergo_module2 :: nil.
    Definition aml2 := resolve_ergo_modules (empty_namespace_ctxt "TEST") ml2.
    (* Eval vm_compute in aml2. *)

    Definition aml3 := elift (fun mc => resolve_ergo_module (snd mc) ergo_module1) aml2.
    (* Eval vm_compute in aml3. *)
  End Examples.
  
End ErgoNameResolution.

