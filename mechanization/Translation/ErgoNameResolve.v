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
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Translation.CTOtoErgo.

Section ErgoNameResolution.

  (** There are three phases to the name resolution in ErgoType files/modules:
- build a per-namespace table containing all the local names mapped to their namespace resolve names
- for a module, resolve imports using the per-namespace table to build a full namespace mapping for that module
- resolve the names within a given module using the full namespace mapping for that module *)

  Definition no_namespace : string := "".
    
  Section NamespaceTable.
    (** Maps local names to absolute names for a given ErgoType module *)
    Definition name_table : Set := list (local_name * absolute_name).

    (** Maps namespaces to the names tables for that namespace *)
    Record namespace_table : Set :=
      mkNamespaceTable
        { namespace_table_types : name_table;
          namespace_table_constants : name_table;
          namespace_table_functions : name_table; }.

    Definition empty_namespace_table : namespace_table :=
      mkNamespaceTable nil nil nil.
  
    Definition one_type_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable ((ln,an)::nil) nil nil.
    Definition one_constant_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil ((ln,an)::nil) nil.
    Definition one_function_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil nil ((ln,an)::nil).

    Definition namespace_table_app (tbl1 tbl2:namespace_table) : namespace_table :=
      mkNamespaceTable
        (app tbl1.(namespace_table_types) tbl2.(namespace_table_types))
        (app tbl1.(namespace_table_constants) tbl2.(namespace_table_constants))
        (app tbl1.(namespace_table_functions) tbl2.(namespace_table_functions)).

    Definition lookup_type_name (loc:location) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_types) ln with
      | None => type_name_not_found_error loc ln
      | Some an => esuccess an
      end.
    Definition lookup_constant_name (loc:location) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_constants) ln with
      | None => variable_name_not_found_error loc ln
      | Some an => esuccess an
      end.
    Definition lookup_function_name (loc:location) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_functions) ln with
      | None => function_name_not_found_error loc ln
      | Some an => esuccess an
      end.

    Definition resolve_type_name (loc:location) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_type_name loc tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.
    Definition resolve_constant_name (loc:location) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_constant_name loc tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.
    Definition resolve_function_name (loc:location) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_function_name loc tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.

    Definition add_type_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        ((ln,an)::tbl.(namespace_table_types))
        tbl.(namespace_table_constants)
        tbl.(namespace_table_functions).
  
    Definition add_constant_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        ((ln,an)::tbl.(namespace_table_constants))
        tbl.(namespace_table_functions).
  
    Definition add_function_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        tbl.(namespace_table_constants)
        ((ln,an)::tbl.(namespace_table_functions)).

  End NamespaceTable.

  Section NamespaceContext.
    Record namespace_ctxt : Set :=
      mkNamespaceCtxt {
          namespace_ctxt_modules : list (namespace_name * namespace_table);
          namespace_ctxt_namespace : namespace_name;
          namespace_ctxt_current : namespace_table;
        }.

    Definition empty_namespace_ctxt (ns:namespace_name) : namespace_ctxt :=
      mkNamespaceCtxt nil ns empty_namespace_table.

    Definition update_namespace_context_modules
               (ctxt:namespace_ctxt)
               (ns:namespace_name)
               (update:namespace_table -> namespace_table) : namespace_ctxt :=
      match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
      | Some t =>
        mkNamespaceCtxt (update_first string_dec ctxt.(namespace_ctxt_modules) ns (update t))
                        ctxt.(namespace_ctxt_namespace)
                        ctxt.(namespace_ctxt_current)
      | None =>
        mkNamespaceCtxt ((ns, update empty_namespace_table) :: ctxt.(namespace_ctxt_modules))
                        ctxt.(namespace_ctxt_namespace)
                        ctxt.(namespace_ctxt_current)
      end.

    Definition update_namespace_context_current
               (ctxt:namespace_ctxt)
               (update:namespace_table -> namespace_table) : namespace_ctxt :=
      mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                      ctxt.(namespace_ctxt_namespace)
                      (update ctxt.(namespace_ctxt_current)).

    Definition add_type_to_namespace_ctxt
               (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_modules ctxt ns (add_type_to_namespace_table ln an).
  
    Definition add_constant_to_namespace_ctxt
               (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_modules ctxt ns (add_constant_to_namespace_table ln an).
  
    Definition add_function_to_namespace_ctxt
               (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_modules ctxt ns (add_function_to_namespace_table ln an).

    Definition add_type_to_namespace_ctxt_current
               (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_current ctxt (add_type_to_namespace_table ln an).
    
    Definition add_constant_to_namespace_ctxt_current
               (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_current ctxt (add_constant_to_namespace_table ln an).
  
    Definition add_function_to_namespace_ctxt_current
               (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
      update_namespace_context_current ctxt (add_function_to_namespace_table ln an).

    Definition new_namespace_scope (ctxt:namespace_ctxt) (ns:namespace_name) :=
      let prev_ns := ctxt.(namespace_ctxt_namespace) in
      let prev_tbl := ctxt.(namespace_ctxt_current) in
      let prev_modules := ctxt.(namespace_ctxt_modules) in
      if string_dec prev_ns no_namespace (* Do not push empty namespace to stack *)
      then
        mkNamespaceCtxt
          prev_modules
          ns
          empty_namespace_table
      else
        match lookup string_dec prev_modules prev_ns with
        | Some t =>
          mkNamespaceCtxt
            (update_first string_dec prev_modules prev_ns (namespace_table_app prev_tbl t))
            ns
            empty_namespace_table
        | None =>
          mkNamespaceCtxt
            ((prev_ns, prev_tbl) :: prev_modules)
            ns
            empty_namespace_table
        end.

    Fixpoint namespace_ctxt_of_ergo_decls
             (ctxt:namespace_ctxt)
             (ns:namespace_name)
             (dls:list lrergo_declaration) : namespace_ctxt :=
      match dls with
      | nil => ctxt
      | DType _ td :: rest =>
        let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
        let ln := td.(type_declaration_name) in
        let an := absolute_name_of_local_name ns ln in
        add_type_to_namespace_ctxt ctxt ns ln an
      | DStmt _ _ :: rest =>
        let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
        ctxt
      | DConstant _ ln cd :: rest =>
        let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
        let an := absolute_name_of_local_name ns ln in
        add_constant_to_namespace_ctxt ctxt ns ln an
      | DFunc _ fd :: rest =>
        let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
        let ln := fd.(function_name) in
        let an := absolute_name_of_local_name ns ln in
        add_function_to_namespace_ctxt ctxt ns ln an
      | DContract _ c :: rest => (* XXX TO BE REVISED *)
        let ctxt := namespace_ctxt_of_ergo_decls ctxt ns rest in
        ctxt
      end.

    Definition namespace_ctxt_of_ergo_module (ctxt:namespace_ctxt) (m:lrergo_module) : namespace_ctxt :=
      namespace_ctxt_of_ergo_decls ctxt m.(module_namespace) m.(module_declarations).

    Definition namespace_ctxt_of_ergo_modules (ctxt:namespace_ctxt) (ml:list lrergo_module) : namespace_ctxt :=
      fold_left namespace_ctxt_of_ergo_module ml ctxt.

  End NamespaceContext.

  Section ResolveImports.
    (** This applies imports *)
    Definition lookup_one_import
               (ctxt:namespace_ctxt)
               (ic:import_decl) : eresult namespace_table :=
      match ic with
      | ImportAll loc ns =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl => esuccess tbl
        | None => import_not_found_error loc ns
        end
      | ImportSelf loc ns =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl => esuccess tbl
        | None => esuccess empty_namespace_table
        end
      | ImportName loc ns ln =>
        match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
        | Some tbl =>
          match lookup string_dec tbl.(namespace_table_types) ln with
          | None => import_name_not_found_error loc ns ln
          | Some an => esuccess (one_type_to_namespace_table ln an)
          end
        | None => import_not_found_error loc ns
        end
      end.

    Definition resolve_one_import
               (ctxt:namespace_ctxt)
               (ic:import_decl) : eresult namespace_ctxt :=
      elift (fun tbl =>
               mkNamespaceCtxt
                 ctxt.(namespace_ctxt_modules)
                 ctxt.(namespace_ctxt_namespace)
                 (namespace_table_app ctxt.(namespace_ctxt_current) tbl))
            (lookup_one_import ctxt ic).
    
    Definition resolve_imports
               (ctxt:namespace_ctxt)
               (imports:list limport_decl) : eresult namespace_ctxt :=
      let proc_one (acc:eresult namespace_ctxt) (import:import_decl) : eresult namespace_ctxt :=
          eolift (fun acc => resolve_one_import acc import) acc
      in
      fold_left proc_one imports (esuccess ctxt).

  End ResolveImports.

  Section NameResolution.
    (** Name resolution for type declarations *)
    Fixpoint resolve_ergo_type
             (tbl:namespace_table)
             (t:lrergo_type) : eresult laergo_type :=
      match t with
      | ErgoTypeAny loc => esuccess (ErgoTypeAny loc)
      | ErgoTypeNone loc => esuccess (ErgoTypeNone loc)
      | ErgoTypeBoolean loc => esuccess (ErgoTypeBoolean loc)
      | ErgoTypeString loc => esuccess (ErgoTypeString loc)
      | ErgoTypeDouble loc => esuccess (ErgoTypeDouble loc)
      | ErgoTypeLong loc => esuccess (ErgoTypeLong loc)
      | ErgoTypeInteger loc => esuccess (ErgoTypeInteger loc)
      | ErgoTypeDateTime loc => esuccess (ErgoTypeDateTime loc)
      | ErgoTypeClassRef loc rn =>
        elift (ErgoTypeClassRef loc)
              (resolve_type_name loc tbl rn)
      | ErgoTypeOption loc t =>
        elift (ErgoTypeOption loc) (resolve_ergo_type tbl t)
      | ErgoTypeRecord loc r =>
        let initial_map := map (fun xy => (fst xy, resolve_ergo_type tbl (snd xy))) r in
        let lifted_map := emaplift (fun xy => elift (fun t => (fst xy, t)) (snd xy)) initial_map in
        elift (ErgoTypeRecord loc) lifted_map
      | ErgoTypeArray loc t =>
        elift (ErgoTypeArray loc) (resolve_ergo_type tbl t)
      | ErgoTypeSum loc t1 t2 =>
        elift2 (ErgoTypeSum loc)
               (resolve_ergo_type tbl t1)
               (resolve_ergo_type tbl t2)
      end.

    Definition resolve_ergo_type_struct
               (tbl:namespace_table)
               (t:list (string * lrergo_type)) : eresult (list (string * laergo_type)) :=
      emaplift (fun xy =>
                  elift (fun t => (fst xy, t)) (resolve_ergo_type tbl (snd xy))) t.

    Definition resolve_extends
               (loc:location)
               (tbl:namespace_table)
               (en:rextends) : eresult aextends :=
      match en with
      | None => esuccess None
      | Some rn => elift Some (resolve_type_name loc tbl rn)
      end.

    Definition resolve_ergo_type_signature
               (tbl:namespace_table)
               (sig:lrergo_type_signature) : eresult laergo_type_signature :=
      let params_types := resolve_ergo_type_struct tbl (sig.(type_signature_params)) in
      let output_type : eresult laergo_type := resolve_ergo_type tbl sig.(type_signature_output) in
      let throws_type : eresult (option laergo_type) :=
          match sig.(type_signature_throws) with
          | None => esuccess None
          | Some throw_ty =>
            elift Some (resolve_ergo_type tbl throw_ty)
          end
      in
      let emits_type : eresult (option laergo_type) :=
          match sig.(type_signature_emits) with
          | None => esuccess None
          | Some emits_ty =>
            elift Some (resolve_ergo_type tbl emits_ty)
          end
      in
      elift4 (mkErgoTypeSignature
                sig.(type_signature_annot))
             params_types
             output_type
             throws_type
           emits_type.

    Definition resolve_ergo_type_clauses
               (tbl:namespace_table)
               (cls:list (string * lrergo_type_signature)) : eresult (list (string * laergo_type_signature)) :=
      emaplift (fun xy => elift (fun r => (fst xy, r))
                                (resolve_ergo_type_signature tbl (snd xy))) cls.

    Definition resolve_ergo_type_declaration_desc
               (loc:location)
               (tbl:namespace_table)
               (d:lrergo_type_declaration_desc) : eresult laergo_type_declaration_desc :=
      match d with
      | ErgoTypeEnum l => esuccess (ErgoTypeEnum l)
      | ErgoTypeTransaction extends_name ergo_type_struct =>
        elift2 ErgoTypeTransaction
               (resolve_extends loc tbl extends_name)
               (resolve_ergo_type_struct tbl ergo_type_struct)
      | ErgoTypeConcept extends_name ergo_type_struct =>
        elift2 ErgoTypeConcept
               (resolve_extends loc tbl extends_name)
               (resolve_ergo_type_struct tbl ergo_type_struct)
      | ErgoTypeEvent extends_name ergo_type_struct =>
        elift2 ErgoTypeEvent
               (resolve_extends loc tbl extends_name)
               (resolve_ergo_type_struct tbl ergo_type_struct)
      | ErgoTypeAsset extends_name ergo_type_struct =>
        elift2 ErgoTypeAsset
               (resolve_extends loc tbl extends_name)
               (resolve_ergo_type_struct tbl ergo_type_struct)
      | ErgoTypeParticipant extends_name ergo_type_struct =>
        elift2 ErgoTypeParticipant
               (resolve_extends loc tbl extends_name)
               (resolve_ergo_type_struct tbl ergo_type_struct)
      | ErgoTypeGlobal ergo_type =>
        elift ErgoTypeGlobal (resolve_ergo_type tbl ergo_type)
      | ErgoTypeFunction ergo_type_signature =>
        elift ErgoTypeFunction
              (resolve_ergo_type_signature tbl ergo_type_signature)
      | ErgoTypeContract template_type state_type clauses_sigs =>
        elift3 ErgoTypeContract
               (resolve_ergo_type tbl template_type)
               (resolve_ergo_type tbl state_type)
               (resolve_ergo_type_clauses tbl clauses_sigs)
      end.

    Definition resolve_ergo_type_declaration
               (module_ns:namespace_name)
               (tbl:namespace_table)
               (decl: lrergo_type_declaration) : eresult laergo_type_declaration :=
      let name := absolute_name_of_local_name module_ns decl.(type_declaration_name) in
      let edecl_desc :=
          resolve_ergo_type_declaration_desc
            decl.(type_declaration_annot) tbl decl.(type_declaration_type)
      in
      elift (fun k => mkErgoTypeDeclaration decl.(type_declaration_annot) name k) edecl_desc.

    (** Name resolution for expressions *)
    Fixpoint resolve_ergo_expr
             (tbl:namespace_table)
             (e:lrergo_expr) : eresult laergo_expr :=
      match e with
      | EThisContract loc => esuccess (EThisContract loc)
      | EThisClause loc => esuccess (EThisClause loc)
      | EThisState loc => esuccess (EThisState loc)
      | EVar loc v => esuccess (EVar loc v)
      | EConst loc d => esuccess (EConst loc d)
      | EArray loc el =>
        let init_el := esuccess nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr tbl e)
              acc
        in
        elift (EArray loc) (fold_right proc_one init_el el)
      | EUnaryOp loc u e =>
        elift (EUnaryOp loc u)
              (resolve_ergo_expr tbl e)
      | EBinaryOp loc b e1 e2 =>
        elift2 (EBinaryOp loc b)
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_expr tbl e2)
      | EIf loc e1 e2 e3 =>
        elift3 (EIf loc)
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_expr tbl e2)
               (resolve_ergo_expr tbl e3)
      | ELet loc v ta e1 e2 =>
        let rta :=
            match ta with
            | None => esuccess None
            | Some ta => elift Some (resolve_ergo_type tbl ta)
            end
        in
        elift3 (ELet loc v)
               rta
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_expr tbl e2)
      | ENew loc cr el =>
        let rcr := resolve_type_name loc tbl cr in
        let init_rec := esuccess nil in
        let proc_one (att:string * lrergo_expr) (acc:eresult (list (string * laergo_expr))) :=
            let attname := fst att in
            let e := resolve_ergo_expr tbl (snd att) in
            elift2 (fun e => fun acc => (attname,e)::acc) e acc
        in
        elift2 (ENew loc) rcr (fold_right proc_one init_rec el)
      | ERecord loc el =>
        let init_rec := esuccess nil in
        let proc_one (att:string * lrergo_expr) (acc:eresult (list (string * laergo_expr))) :=
            let attname := fst att in
            let e := resolve_ergo_expr tbl (snd att) in
            elift2 (fun e => fun acc => (attname,e)::acc) e acc
        in
        elift (ERecord loc) (fold_right proc_one init_rec el)
      | ECallFun loc fname el =>
        let rfname := resolve_function_name loc tbl (None,fname) in
        let init_el := esuccess nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr tbl e)
              acc
        in
        elift2 (ECallFun loc) rfname (fold_right proc_one init_el el)
      | EMatch loc e0 ecases edefault =>
        let ec0 := resolve_ergo_expr tbl e0 in
        let eccases :=
            let proc_one acc ecase :=
                eolift
                  (fun acc =>
                     elift (fun x => (fst ecase, x)::acc)
                           (resolve_ergo_expr tbl (snd ecase))) acc
            in
            fold_left proc_one ecases (esuccess nil)
        in
        let ecdefault := resolve_ergo_expr tbl edefault in
        eolift
          (fun ec0 : laergo_expr =>
             eolift
               (fun eccases : list (ergo_pattern * laergo_expr) =>
                  elift
                    (fun ecdefault : laergo_expr =>
                    EMatch loc ec0 eccases ecdefault)
                    ecdefault) eccases) ec0
      | EForeach loc foreachs econd e2 =>
        let re2 := resolve_ergo_expr tbl e2 in
        let recond :=
            match econd with
            | None => esuccess None
            | Some econd => elift Some (resolve_ergo_expr tbl econd)
            end
        in
        let init_e := esuccess nil in
        let proc_one
              (foreach:string * lrergo_expr)
              (acc:eresult (list (string * laergo_expr)))
            : eresult (list (string * laergo_expr)) :=
            let v := fst foreach in
            let e := resolve_ergo_expr tbl (snd foreach) in
            elift2 (fun e => fun acc => (v,e)::acc)
                 e
                 acc
        in
        elift3 (EForeach loc)
               (fold_right proc_one init_e foreachs)
               recond
               re2
      end.

    (** Name resolution for statements *)
    Fixpoint resolve_ergo_stmt
             (tbl:namespace_table)
             (e:lrergo_stmt) : eresult laergo_stmt :=
      match e with
      | SReturn loc e => elift (SReturn loc) (resolve_ergo_expr tbl e)
      | SFunReturn loc e => elift (SFunReturn loc) (resolve_ergo_expr tbl e)
      | SThrow loc e =>  elift (SThrow loc) (resolve_ergo_expr tbl e)
      | SCallClause loc fname el =>
        let rfname := resolve_function_name loc tbl (None,fname) in
        let init_el := esuccess nil in
        let proc_one (e:lrergo_expr) (acc:eresult (list laergo_expr)) : eresult (list laergo_expr) :=
            elift2
              cons
              (resolve_ergo_expr tbl e)
              acc
        in
        elift2 (SCallClause loc) rfname (fold_right proc_one init_el el)
      | SSetState loc e1 s2 =>
        elift2 (SSetState loc)
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_stmt tbl s2)
      | SEmit loc e1 s2 =>
        elift2 (SEmit loc)
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_stmt tbl s2)
      | SLet loc v ta e1 s2 =>
        let rta :=
            match ta with
            | None => esuccess None
            | Some ta => elift Some (resolve_ergo_type tbl ta)
            end
        in
        elift3 (SLet loc v)
               rta
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_stmt tbl s2)
      | SIf loc e1 s2 s3 =>
        elift3 (SIf loc)
               (resolve_ergo_expr tbl e1)
               (resolve_ergo_stmt tbl s2)
               (resolve_ergo_stmt tbl s3)
      | SEnforce loc e1 os2 s3 =>
        let rs2 :=
            match os2 with
            | None => esuccess None
            | Some s2 => elift Some (resolve_ergo_stmt tbl s2)
            end
        in
        elift3 (SEnforce loc)
               (resolve_ergo_expr tbl e1)
               rs2
               (resolve_ergo_stmt tbl s3)
      | SMatch loc e0 scases sdefault =>
        let ec0 := resolve_ergo_expr tbl e0 in
        let sccases :=
            let proc_one acc scase :=
                eolift
                  (fun acc =>
                     elift (fun x => (fst scase, x)::acc)
                           (resolve_ergo_stmt tbl (snd scase))) acc
            in
            fold_left proc_one scases (esuccess nil)
        in
        let scdefault := resolve_ergo_stmt tbl sdefault in
        eolift
          (fun ec0 : laergo_expr =>
             eolift
               (fun sccases : list (ergo_pattern * laergo_stmt) =>
                  elift
                    (fun scdefault : laergo_stmt =>
                    SMatch loc ec0 sccases scdefault)
                    scdefault) sccases) ec0
      end.

    (** Name resolution for lambdas *)

    Definition resolve_ergo_function
               (module_ns:namespace_name)
               (tbl:namespace_table)
               (f:lrergo_function) : eresult laergo_function :=
      let loc := f.(function_annot) in
      let rfname := absolute_name_of_local_name module_ns f.(function_name) in
      let rbody :=
          match f.(function_body) with
          | None => esuccess None
          | Some body => elift Some (resolve_ergo_stmt tbl body)
          end
      in
      elift2 (mkFunc loc rfname)
             (resolve_ergo_type_signature tbl f.(function_sig))
             rbody.
    
    Definition resolve_ergo_clause
               (module_ns:namespace_name)
               (tbl:namespace_table)
               (c:ergo_clause) : eresult laergo_clause :=
      let loc := c.(clause_annot) in
      let rcname := c.(clause_name) in
      let rbody :=
          match c.(clause_body) with
          | None => esuccess None
          | Some body => elift Some (resolve_ergo_stmt tbl body)
          end
      in
      elift2 (mkClause loc rcname)
             (resolve_ergo_type_signature tbl c.(clause_sig))
             rbody.

    Definition resolve_ergo_clauses
               (module_ns:namespace_name)
               (tbl:namespace_table)
               (cl:list ergo_clause) : eresult (list laergo_clause) :=
      emaplift (resolve_ergo_clause module_ns tbl) cl.

    Definition resolve_ergo_contract
               (module_ns:namespace_name)
               (tbl:namespace_table)
               (c:lrergo_contract) : eresult laergo_contract :=
      let loc := c.(contract_annot) in
      let rcname := absolute_name_of_local_name module_ns c.(contract_name) in
      let rtemplate := resolve_ergo_type tbl c.(contract_template) in
      let rstate :=
          match c.(contract_state) with
          | None => esuccess None
          | Some state => elift Some (resolve_ergo_type tbl state)
          end
      in
      elift3 (mkContract loc rcname)
             rtemplate
             rstate
             (resolve_ergo_clauses module_ns tbl c.(contract_clauses)).

    Definition resolve_ergo_declaration
               (ctxt:namespace_ctxt)
               (d:lrergo_declaration)
      : eresult (laergo_declaration * namespace_ctxt) :=
      let module_ns : namespace_name := ctxt.(namespace_ctxt_namespace) in
      let tbl : namespace_table := ctxt.(namespace_ctxt_current) in
      match d with
      | DType loc td =>
        let ln := td.(type_declaration_name) in
        let an := absolute_name_of_local_name module_ns ln in
        let ctxt := add_type_to_namespace_ctxt_current ctxt ln an in
        elift (fun x => (DType loc x, ctxt)) (resolve_ergo_type_declaration module_ns tbl td)
      | DStmt loc st =>
        elift (fun x => (DStmt loc x, ctxt)) (resolve_ergo_stmt tbl st)
      | DConstant loc ln e =>
        let an := absolute_name_of_local_name module_ns ln in
        let ctxt := add_constant_to_namespace_ctxt_current ctxt ln an in
        elift (fun x => (DConstant loc ln x, ctxt)) (resolve_ergo_expr tbl e)
      | DFunc loc fd =>
        let ln := fd.(function_name) in
        let an := absolute_name_of_local_name module_ns ln in
        let ctxt := add_function_to_namespace_ctxt_current ctxt ln an in (* XXX TBD *)
        elift (fun x => (DFunc loc x, ctxt)) (resolve_ergo_function module_ns tbl fd)
      | DContract loc c => (* XXX TO BE REVISED *)
        let ctxt := ctxt in
        elift (fun x => (DContract loc x, ctxt)) (resolve_ergo_contract module_ns tbl c)
      end.

    Definition resolve_ergo_declarations
               (ctxt:namespace_ctxt)
               (decls: list lrergo_declaration)
      : eresult (list ergo_declaration * namespace_ctxt) :=
      elift_context_fold_left
        resolve_ergo_declaration
        decls
        ctxt.

  End NameResolution.

  Section Top.
    Definition init_namespace_ctxt : namespace_ctxt :=
      empty_namespace_ctxt no_namespace.

    Definition init_namespace_ctxt_from_modules (ml:list lrergo_module) :=
      namespace_ctxt_of_ergo_modules init_namespace_ctxt ml.

    Definition hyperledger_namespace : string := "org.hyperledger.composer.system"%string.
    Definition stdlib_namespace : string := "org.accordproject.ergo.stdlib"%string.
    
    Definition is_builtin_import (ns:namespace_name) : bool :=
      if string_dec ns hyperledger_namespace
      then true
      else if string_dec ns stdlib_namespace
           then true
           else false.

    (* Resolve a CTO package *)
    Definition resolve_cto_package
               (ctxt:namespace_ctxt)
               (cto:lrcto_package) : eresult (laergo_module * namespace_ctxt) :=
      let m := cto_package_to_ergo_module cto in
      let module_ns := m.(module_namespace) in
      let ctxt := new_namespace_scope ctxt module_ns in
      let ctxt := namespace_ctxt_of_ergo_module ctxt m in (* XXX Pre-populate namespace for CTO modules to handle not-yet-declared names *)
      let imports :=
          if is_builtin_import module_ns
          then app m.(module_imports) (ImportSelf dummy_location module_ns :: nil)
          else
           (* Add built-in modules to import, first.
              Make sure to add current namespace to the list of imports - i.e., import self. *)
          (ImportAll dummy_location hyperledger_namespace)
            ::(app m.(module_imports) (ImportSelf dummy_location module_ns :: nil))
      in
      let rctxt := resolve_imports ctxt imports in
      eolift (fun ctxt =>
                elift
                  (fun nc =>
                     (mkModule
                        m.(module_annot)
                        module_ns
                        nil
                        (fst nc), snd nc))
                  (resolve_ergo_declarations
                     ctxt
                     m.(module_declarations))) rctxt.

    Definition resolve_ergo_module
               (ctxt:namespace_ctxt)
               (m:lrergo_module) : eresult (laergo_module * namespace_ctxt) :=
      let module_ns := m.(module_namespace) in
      let ctxt := new_namespace_scope ctxt module_ns in
      let imports :=
          if is_builtin_import module_ns
          then app m.(module_imports) (ImportSelf dummy_location module_ns :: nil)
          else
           (* Add built-in modules to import, first.
              Make sure to add current namespace to the list of imports - i.e., import self. *)
          (ImportAll dummy_location hyperledger_namespace)
            ::(ImportAll dummy_location stdlib_namespace)
            ::(app m.(module_imports) (ImportSelf dummy_location module_ns :: nil))
      in
      let rctxt := resolve_imports ctxt imports in
      eolift (fun ctxt =>
                elift
                  (fun nc =>
                     (mkModule
                        m.(module_annot)
                        module_ns
                        nil
                        (fst nc), snd nc))
                  (resolve_ergo_declarations
                     ctxt
                     m.(module_declarations))) rctxt.

    Definition resolve_ergo_modules
               (ctxt:namespace_ctxt)
               (ml:list lrergo_module) : eresult (list laergo_module * namespace_ctxt) :=
      elift_context_fold_left
        resolve_ergo_module
        ml
        ctxt.

    Definition resolve_ergo_input
               (ctxt:namespace_ctxt)
               (input:lrergo_input) : eresult (laergo_module * namespace_ctxt) :=
      match input with
      | InputCTO cto =>
        resolve_cto_package ctxt cto
      | InputErgo m =>
        resolve_ergo_module ctxt m
      end.
    
    Definition resolve_ergo_inputs
               (ctxt:namespace_ctxt)
               (il:list lrergo_input) : eresult (list laergo_module * namespace_ctxt) :=
      elift_context_fold_left
        resolve_ergo_input
        il
        ctxt.

  End Top.

  Section Examples.
    Local Open Scope string.
    Definition ergo_typed1 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_location
        "c1"
        (ErgoTypeConcept
           None
           (("a", ErgoTypeBoolean dummy_location)
              ::("b", (ErgoTypeClassRef dummy_location (None, "c3")))::nil)).

    Definition ergo_typed2 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_location
        "c2"
        (ErgoTypeConcept
           None
           (("c", ErgoTypeBoolean dummy_location)
              ::("d", (ErgoTypeClassRef dummy_location (None, "c1")))::nil)).

    Definition ergo_funcd1 : lrergo_function :=
      mkFunc
        dummy_location
        "addFee"
        (mkErgoTypeSignature
           dummy_location
           nil
           (ErgoTypeBoolean dummy_location)
           None
           None)
        None.
    
    Definition ergo_funcd2 : lrergo_function :=
      mkFunc
        dummy_location
        "addFee2"
        (mkErgoTypeSignature
           dummy_location
           nil
           (ErgoTypeBoolean dummy_location)
           None
           None)
        (Some (SFunReturn dummy_location (ECallFun dummy_location "addFee" nil))).

    Definition ergo_clause2 : lrergo_clause :=
      mkClause
        dummy_location
        "addFee2"
        (mkErgoTypeSignature
           dummy_location
           nil
           (ErgoTypeBoolean dummy_location)
           None
           None)
        (Some (SReturn dummy_location (ECallFun dummy_location "addFee" nil))).

    Definition ergo_contractd1 : lrergo_contract :=
      mkContract
        dummy_location
        "MyContract"
        (ErgoTypeBoolean dummy_location)
        None
        (ergo_clause2::nil).
    
    Definition ergo_module1 : lrergo_module :=
      mkModule
        dummy_location
        "n1"
        ((ImportAll dummy_location "n2")::nil)
        (DFunc dummy_location ergo_funcd1
               ::DContract dummy_location ergo_contractd1
               ::DType dummy_location ergo_typed1
               ::DType dummy_location ergo_typed2::nil).
    
    Definition ergo_typed3 : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_location
        "c3"
        (ErgoTypeConcept
           None
           (("a", ErgoTypeBoolean dummy_location)
              ::("b", ErgoTypeString dummy_location)::nil)).

    Definition ergo_typed_top : lrergo_type_declaration :=
      mkErgoTypeDeclaration
        dummy_location
        "top"
        (ErgoTypeGlobal
           (ErgoTypeAny dummy_location)).

    Definition ergo_module2 : lrergo_module :=
      mkModule
        dummy_location "n2" nil (DType dummy_location ergo_typed3::nil).

    Definition ergo_hl : lrergo_module :=
      mkModule
        dummy_location hyperledger_namespace nil (DType dummy_location ergo_typed_top::nil).

    Definition ergo_stdlib : lrergo_module :=
      mkModule
        dummy_location stdlib_namespace nil (DType dummy_location ergo_typed_top::nil).

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

