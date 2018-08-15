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
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Result.

Section NamespaceContext.

  Section NameTable.
    (** Maps local names to absolute names for a given ErgoType module *)
    Definition name_table : Set := list (local_name * absolute_name).

    (** Maps namespaces to the names tables for that namespace *)
    Record namespace_table : Set :=
      mkNamespaceTable
        { namespace_table_types : name_table;
          namespace_table_constants : name_table;
          namespace_table_functions : name_table;
          namespace_table_contracts : name_table; }.

    Definition empty_namespace_table : namespace_table :=
      mkNamespaceTable nil nil nil nil.

    Definition one_type_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable ((ln,an)::nil) nil nil nil.
    Definition one_constant_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil ((ln,an)::nil) nil nil.
    Definition one_function_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil nil ((ln,an)::nil) nil.
    Definition one_contract_to_namespace_table (ln:local_name) (an:absolute_name) : namespace_table :=
      mkNamespaceTable nil nil nil ((ln,an)::nil).

    Definition namespace_table_app (tbl1 tbl2:namespace_table) : namespace_table :=
      mkNamespaceTable
        (app tbl1.(namespace_table_types) tbl2.(namespace_table_types))
        (app tbl1.(namespace_table_constants) tbl2.(namespace_table_constants))
        (app tbl1.(namespace_table_functions) tbl2.(namespace_table_functions))
        (app tbl1.(namespace_table_contracts) tbl2.(namespace_table_contracts)).

    Definition lookup_type_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_types) ln with
      | None => type_name_not_found_error prov ln
      | Some an => esuccess an
      end.
    Definition lookup_constant_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_constants) ln with
      | None => variable_name_not_found_error prov ln
      | Some an => esuccess an
      end.
    Definition lookup_function_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_functions) ln with
      | None => function_name_not_found_error prov ln
      | Some an => esuccess an
      end.
    Definition lookup_contract_name (prov:provenance) (tbl:namespace_table) (ln:local_name) : eresult absolute_name :=
      match lookup string_dec tbl.(namespace_table_contracts) ln with
      | None => contract_name_not_found_error prov ln
      | Some an => esuccess an
      end.

    Definition resolve_type_name (prov:provenance) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_type_name prov tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.
    Definition resolve_constant_name (prov:provenance) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_constant_name prov tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.
    Definition resolve_function_name (prov:provenance) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_function_name prov tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.
    Definition resolve_contract_name (prov:provenance) (tbl:namespace_table) (rn:relative_name) :=
      match fst rn with
      | None => lookup_contract_name prov tbl (snd rn)
      | Some ns => esuccess (absolute_name_of_local_name ns (snd rn))
      end.

    Definition add_type_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        ((ln,an)::tbl.(namespace_table_types))
        tbl.(namespace_table_constants)
        tbl.(namespace_table_functions)
        tbl.(namespace_table_contracts).
    Definition add_constant_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        ((ln,an)::tbl.(namespace_table_constants))
        tbl.(namespace_table_functions)
        tbl.(namespace_table_contracts).
    Definition add_function_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable
        tbl.(namespace_table_types)
        tbl.(namespace_table_constants)
        ((ln,an)::tbl.(namespace_table_functions))
        tbl.(namespace_table_contracts).
    Definition add_contract_to_namespace_table (ln:local_name) (an:absolute_name) (tbl:namespace_table) :=
      mkNamespaceTable 
        tbl.(namespace_table_types)
        tbl.(namespace_table_constants)
        tbl.(namespace_table_functions)
        ((ln,an)::tbl.(namespace_table_contracts)).
  End NameTable.

  Definition enum_ctxt : Set := list string.
  Record namespace_ctxt : Set :=
    mkNamespaceCtxt {
        namespace_ctxt_modules : list (namespace_name * namespace_table);
        namespace_ctxt_namespace : namespace_name;
        namespace_ctxt_current : namespace_table;
        namespace_ctxt_enums : enum_ctxt;
      }.

  Definition empty_namespace_ctxt (ns:namespace_name) : namespace_ctxt :=
    mkNamespaceCtxt nil ns empty_namespace_table nil.

  Definition update_namespace_context_modules
             (ctxt:namespace_ctxt)
             (ns:namespace_name)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    match lookup string_dec ctxt.(namespace_ctxt_modules) ns with
    | Some t =>
      mkNamespaceCtxt (update_first string_dec ctxt.(namespace_ctxt_modules) ns (update t))
                      ctxt.(namespace_ctxt_namespace)
                      ctxt.(namespace_ctxt_current)
                      ctxt.(namespace_ctxt_enums)
    | None =>
      mkNamespaceCtxt ((ns, update empty_namespace_table) :: ctxt.(namespace_ctxt_modules))
                      ctxt.(namespace_ctxt_namespace)
                      ctxt.(namespace_ctxt_current)
                      ctxt.(namespace_ctxt_enums)
    end.

  Definition update_namespace_context_current
             (ctxt:namespace_ctxt)
             (update:namespace_table -> namespace_table) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    (update ctxt.(namespace_ctxt_current))
                    ctxt.(namespace_ctxt_enums).
  
  Definition update_namespace_context_enums
             (ctxt:namespace_ctxt)
             (ectxt:enum_ctxt) : namespace_ctxt :=
    mkNamespaceCtxt ctxt.(namespace_ctxt_modules)
                    ctxt.(namespace_ctxt_namespace)
                    ctxt.(namespace_ctxt_current)
                    ectxt.
    
  Definition add_type_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_type_to_namespace_table ln an).
  
  Definition add_constant_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_constant_to_namespace_table ln an).
  
  Definition add_function_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_function_to_namespace_table ln an).

  Definition add_contract_to_namespace_ctxt
             (ctxt:namespace_ctxt) (ns:namespace_name) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_modules ctxt ns (add_contract_to_namespace_table ln an).

  Definition add_type_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current ctxt (add_type_to_namespace_table ln an).
    
  Definition add_constant_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current ctxt (add_constant_to_namespace_table ln an).
  
  Definition add_function_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current ctxt (add_function_to_namespace_table ln an).

  Definition add_contract_to_namespace_ctxt_current
             (ctxt:namespace_ctxt) (ln:local_name) (an:absolute_name) :=
    update_namespace_context_current ctxt (add_contract_to_namespace_table ln an).

  Definition new_namespace_scope (ctxt:namespace_ctxt) (ns:namespace_name) : namespace_ctxt :=
    let prev_ns := ctxt.(namespace_ctxt_namespace) in
    let prev_tbl := ctxt.(namespace_ctxt_current) in
    let prev_modules := ctxt.(namespace_ctxt_modules) in
    let prev_enums := ctxt.(namespace_ctxt_enums) in
    if string_dec prev_ns no_namespace (* Do not push empty namespace to stack *)
    then
      mkNamespaceCtxt
        prev_modules
        ns
        empty_namespace_table
        prev_enums
    else
      match lookup string_dec prev_modules prev_ns with
      | Some t =>
        mkNamespaceCtxt
          (update_first string_dec prev_modules prev_ns (namespace_table_app prev_tbl t))
          ns
          empty_namespace_table
          prev_enums
      | None =>
        mkNamespaceCtxt
          ((prev_ns, prev_tbl) :: prev_modules)
          ns
          empty_namespace_table
          prev_enums
      end.

  Definition local_namespace_scope (ctxt:namespace_ctxt) (ns:namespace_name) : namespace_ctxt :=
    let prev_ns := ctxt.(namespace_ctxt_namespace) in
    let prev_tbl := ctxt.(namespace_ctxt_current) in
    let prev_modules := ctxt.(namespace_ctxt_modules) in
    let prev_enums := ctxt.(namespace_ctxt_enums) in
    mkNamespaceCtxt
      prev_modules
      ns
      prev_tbl
      prev_enums.

End NamespaceContext.

