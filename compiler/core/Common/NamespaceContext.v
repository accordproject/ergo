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
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.

Section NamespaceContext.

  Section NameTable.
    (** Maps local names to absolute names for a given ErgoType module *)
    Inductive enum_flag :=
    | EnumNone : enum_flag
    | EnumValue : data -> enum_flag
    | EnumType : list (string * data) -> enum_flag.
    Definition name_table : Set := list (local_name * (absolute_name * enum_flag)).

    (** Maps namespaces to the names tables for that namespace *)
    Record namespace_table : Set :=
      mkNamespaceTable
        { namespace_table_types : name_table;
          namespace_table_constants : name_table;
          namespace_table_functions : name_table;
          namespace_table_contracts : name_table; }.

    Definition empty_namespace_table : namespace_table :=
      mkNamespaceTable nil nil nil nil.

    Definition import_one_type_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable ((ln,(an,EnumNone))::nil) nil nil nil.
    Definition import_one_enum_type_to_namespace_table (ln:local_name) (an:absolute_name) (el:list (string * data)) : namespace_table :=
      let cs := map (fun ef : string * data => let (ename,d) := ef in
                               (ename, (absolute_name_of_local_name an ename, EnumValue d))) el in
      mkNamespaceTable ((ln,(an,EnumType el))::nil) cs nil nil.
    Definition import_one_constant_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil ((ln,(an,EnumNone))::nil) nil nil.
    Definition import_one_function_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil nil ((ln,(an,EnumNone))::nil) nil.
    Definition import_one_contract_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil nil nil ((ln,(an,EnumNone))::nil).

    Definition namespace_table_app (tbl1 tbl2:namespace_table) : namespace_table :=
      mkNamespaceTable
        (app tbl1.(namespace_table_types) tbl2.(namespace_table_types))
        (app tbl1.(namespace_table_constants) tbl2.(namespace_table_constants))
        (app tbl1.(namespace_table_functions) tbl2.(namespace_table_functions))
        (app tbl1.(namespace_table_contracts) tbl2.(namespace_table_contracts)).

    Definition lookup_type_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_types) ln with
      | None => type_name_not_found_error prov ln
      | Some an => esuccess (fst an) nil
      end.

    Definition lookup_constant_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_constants) ln with
      | None => variable_name_not_found_error prov ln
      | Some (an,EnumNone) => esuccess an nil
      | Some (_,_) => variable_name_not_found_error prov ln
      end.
    Definition lookup_econstant_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult (absolute_name * data) :=
      match lookup string_dec tbl.(namespace_table_constants) ln with
      | None => enum_name_not_found_error prov ln
      | Some (an,EnumValue d) => esuccess (an, d) nil
      | Some (_, _) => enum_name_not_found_error prov ln
      end.
    Definition lookup_function_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_functions) ln with
      | None => function_name_not_found_error prov ln
      | Some an => esuccess (fst an) nil
      end.
    Definition lookup_contract_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_contracts) ln with
      | None => contract_name_not_found_error prov ln
      | Some an => esuccess (fst an) nil
      end.

    Definition add_type_to_namespace_table (ln:local_name) (an:absolute_name) (ef:enum_flag) (tbl:namespace_table) :=
      mkNamespaceTable
        ((ln,(an,ef))::tbl.(namespace_table_types))
        tbl.(namespace_table_constants)
        tbl.(namespace_table_functions)
              tbl.(namespace_table_contracts).
    Definition add_constant_to_namespace_table (ln:local_name) (an:absolute_name) (ef:enum_flag) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        ((ln,(an,ef))::tbl.(namespace_table_constants))
        tbl.(namespace_table_functions)
        tbl.(namespace_table_contracts).
    Definition add_constants_to_namespace_table (lns:list (local_name * (absolute_name * enum_flag))) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        (lns ++ tbl.(namespace_table_constants))
        tbl.(namespace_table_functions)
        tbl.(namespace_table_contracts).
    Definition hide_constant_from_namespace_table (ln:local_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        (filter (fun xy => if string_dec ln (fst xy) then false else true) tbl.(namespace_table_constants))
        tbl.(namespace_table_functions)
        tbl.(namespace_table_contracts).
    Definition add_function_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        tbl.(namespace_table_constants)
        ((ln,(an,EnumNone))::tbl.(namespace_table_functions))
        tbl.(namespace_table_contracts).
    Definition add_contract_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable 
        tbl.(namespace_table_types)
        tbl.(namespace_table_constants)
        tbl.(namespace_table_functions)
        ((ln,(an,EnumNone))::tbl.(namespace_table_contracts)).
  End NameTable.

  Definition abstract_ctxt : Set := list string.
  Record namespace_ctxt : Set :=
    mkNamespaceCtxt {
        namespace_ctxt_modules : list (namespace_name * namespace_table);
        namespace_ctxt_namespace : namespace_name;
        namespace_ctxt_current_module : namespace_table;
        namespace_ctxt_current_in_scope : namespace_table;
        namespace_ctxt_abstract : abstract_ctxt;
      }.

  Definition empty_namespace_ctxt (ns:namespace_name) : namespace_ctxt :=
    mkNamespaceCtxt nil ns empty_namespace_table empty_namespace_table nil.

  Definition update_namespace_context_modules
             (ctxt:namespace_ctxt)
             (ns:namespace_name)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
    | Some t =>
      mkNamespaceCtxt (update_first string_dec ctxt.(namespace_ctxt_modules) ns (update t))
                      ctxt.(namespace_ctxt_namespace)
                      ctxt.(namespace_ctxt_current_module)
                      ctxt.(namespace_ctxt_current_in_scope)
                      ctxt.(namespace_ctxt_abstract)
    | None =>
      mkNamespaceCtxt ((ns, update empty_namespace_table) :: ctxt.(namespace_ctxt_modules))
                      ctxt.(namespace_ctxt_namespace)
                      ctxt.(namespace_ctxt_current_module)
                      ctxt.(namespace_ctxt_current_in_scope)
                      ctxt.(namespace_ctxt_abstract)
    end.

  Definition update_namespace_context_current_module
             (ctxt:namespace_ctxt)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    (update ctxt.(namespace_ctxt_current_module))
                    ctxt.(namespace_ctxt_current_in_scope)
                    ctxt.(namespace_ctxt_abstract).
  
  Definition update_namespace_context_current_in_scope
             (ctxt:namespace_ctxt)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    ctxt.(namespace_ctxt_current_module)
                    (update ctxt.(namespace_ctxt_current_in_scope))
                    ctxt.(namespace_ctxt_abstract).

  Definition update_namespace_context_current_both
             (ctxt:namespace_ctxt)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    (update ctxt.(namespace_ctxt_current_module))
                    (update ctxt.(namespace_ctxt_current_in_scope))
                    ctxt.(namespace_ctxt_abstract).

  Definition update_namespace_context_abstract
             (ctxt:namespace_ctxt)
             (actxt:abstract_ctxt) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    ctxt.(namespace_ctxt_current_module)
                    ctxt.(namespace_ctxt_current_in_scope)
                    actxt.
    
  Definition add_type_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) (ef:enum_flag) :=
    update_namespace_context_modules ctxt ns (add_type_to_namespace_table ln an ef).

  Definition add_constant_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (ef:enum_flag) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_constant_to_namespace_table ln an ef).

  Definition add_function_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_function_to_namespace_table ln an).

  Definition add_contract_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_contract_to_namespace_table ln an).

  Definition add_type_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) (ef:enum_flag) :=
    update_namespace_context_current_both ctxt (add_type_to_namespace_table ln an ef).

  Definition add_constant_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) (ef:enum_flag) :=
    update_namespace_context_current_both ctxt (add_constant_to_namespace_table ln an ef).

  Definition add_econstants_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ens:namespace_name)
             (lns:list (local_name * (absolute_name * enum_flag))) : namespace_ctxt :=
    let ctxt :=
        fold_left (fun ctxt xyz =>
                     let '(ln,(an,ef)):= xyz in
                     update_namespace_context_current_both ctxt (add_constant_to_namespace_table ln an ef))
                  lns ctxt
    in
    (update_namespace_context_modules ctxt ens (add_constants_to_namespace_table lns)).

  Definition hide_constant_from_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) :=
    update_namespace_context_current_both ctxt (hide_constant_from_namespace_table ln).

  Definition hide_constants_from_namespace_ctxt_current
             (ctxt:namespace_ctxt) (lns:list local_name) : namespace_ctxt :=
    fold_left hide_constant_from_namespace_ctxt_current lns ctxt.

  Definition add_function_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current_both ctxt (add_function_to_namespace_table ln an).

  Definition add_contract_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current_both ctxt (add_contract_to_namespace_table ln an).

  Definition new_namespace_scope (ctxt:namespace_ctxt) (ns:namespace_name) : namespace_ctxt :=
    let prev_ns := ctxt.(namespace_ctxt_namespace) in
    let prev_tbl_current_module := ctxt.(namespace_ctxt_current_module) in
    let prev_modules := ctxt.(namespace_ctxt_modules) in
    let prev_abstract := ctxt.(namespace_ctxt_abstract) in
    if string_dec prev_ns no_namespace (* Do not push empty namespace to stack *)
    then
      mkNamespaceCtxt
        prev_modules
        ns
        empty_namespace_table
        empty_namespace_table
        prev_abstract
    else
      match lookup string_dec prev_modules prev_ns with
      | Some t =>
        mkNamespaceCtxt
          (update_first string_dec prev_modules prev_ns (namespace_table_app prev_tbl_current_module t))
          ns
          empty_namespace_table
          empty_namespace_table
          prev_abstract
      | None =>
        mkNamespaceCtxt
          ((prev_ns, prev_tbl_current_module) :: prev_modules)
          ns
          empty_namespace_table
          empty_namespace_table
          prev_abstract
      end.

  Definition local_namespace_scope (ctxt:namespace_ctxt) (ns:namespace_name) : namespace_ctxt :=
    let prev_ns := ctxt.(namespace_ctxt_namespace) in
    let prev_tbl_current_module := ctxt.(namespace_ctxt_current_module) in
    let prev_tbl_current_in_scope := ctxt.(namespace_ctxt_current_in_scope) in
    let prev_modules := ctxt.(namespace_ctxt_modules) in
    let prev_abstract := ctxt.(namespace_ctxt_abstract) in
    mkNamespaceCtxt
      prev_modules
      ns
      prev_tbl_current_module
      prev_tbl_current_in_scope
      prev_abstract.

  Definition verify_name {A}
             (f_lookup: provenance -> namespace_table -> local_name -> eresult A)
             (prov:provenance)
             (ctxt:namespace_ctxt)
             (ns:namespace_name)
             (ln:local_name) : eresult A :=
    let current_ns := ctxt.(namespace_ctxt_namespace) in
    let current_tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    let all_modules := (current_ns, current_tbl) :: ctxt.(namespace_ctxt_modules) in
    match lookup string_dec all_modules ns with
    | None => namespace_not_found_error prov ns
    | Some tbl => f_lookup prov tbl ln
    end.

  Definition verify_type_name (prov:provenance) (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) :=
    verify_name lookup_type_name prov ctxt ns ln.
  Definition verify_constant_name (prov:provenance) (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) :=
    verify_name lookup_constant_name prov ctxt ns ln.
  Definition verify_econstant_name (prov:provenance) (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) :=
    verify_name lookup_econstant_name prov ctxt ns ln.
  Definition verify_function_name (prov:provenance) (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) :=
    verify_name lookup_function_name prov ctxt ns ln.
  Definition verify_contract_name (prov:provenance) (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) :=
    verify_name lookup_contract_name prov ctxt ns ln.

  Definition resolve_type_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    let tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    match fst rn with
    | None => lookup_type_name prov tbl (snd rn)
    | Some ns => verify_type_name prov ctxt ns (snd rn)
    end.
  Definition resolve_constant_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    let tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    match fst rn with
    | None => lookup_constant_name prov tbl (snd rn)
    | Some ns => verify_constant_name prov ctxt ns (snd rn)
    end.
  Definition resolve_econstant_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    let tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    match fst rn with
    | None => lookup_econstant_name prov tbl (snd rn)
    | Some ns => verify_econstant_name prov ctxt ns (snd rn)
    end.
  Definition resolve_all_constant_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    elift_fail (fun _ => elift fst (resolve_econstant_name prov ctxt rn))
               (resolve_constant_name prov ctxt rn).
  Definition resolve_function_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    let tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    match fst rn with
    | None => lookup_function_name prov tbl (snd rn)
    | Some ns => verify_function_name prov ctxt ns (snd rn)
    end.
  Definition resolve_contract_name (prov:provenance) (ctxt:namespace_ctxt) (rn:relative_name) :=
    let tbl : namespace_table := ctxt.(namespace_ctxt_current_in_scope) in
    match fst rn with
    | None => lookup_contract_name prov tbl (snd rn)
    | Some ns => verify_contract_name prov ctxt ns (snd rn)
    end.

End NamespaceContext.

