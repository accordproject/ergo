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

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Types.ErgoTypetoErgoCType.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheckContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCStdlib.
Require Import ErgoSpec.Translation.ErgoNameResolve.

Section ErgoCompContext.
  Context {bm : brand_model}.

  Definition function_group_env : Set := list (string * list (string * ergoc_function)).
  
  Record compilation_context : Set :=
    mkCompCtxt {
        compilation_context_namespace: namespace_ctxt;                     (**r for name resolution *)
        compilation_context_function_env : list (string * ergoc_function); (**r functions in scope *)
        compilation_context_function_group_env : function_group_env;       (**r functions groups in scope *)
        compilation_context_global_env : list (string * ergoc_expr);       (**r global variables in scope *)
        compilation_context_local_env : list (string * ergoc_expr);        (**r local variables in scope *)
        compilation_context_params_env : list string;                      (**r function parameters in scope *)
        compilation_context_current_contract : option string;              (**r current contract in scope if any *)
        compilation_context_current_clause : option string;                (**r current clause in scope if any *)
        compilation_context_type_ctxt : type_context;                      (**r the type context *)
        compilation_context_type_decls : list laergo_type_declaration;     (**r type declarations *)
        compilation_context_new_type_decls : list laergo_type_declaration; (**r new type declarations *)
        compilation_context_warnings : list ewarning;                      (**r warnings up to that point *)
      }.

  Definition namespace_ctxt_of_compilation_context (ctxt:compilation_context) : namespace_ctxt :=
    ctxt.(compilation_context_namespace).

  Definition compilation_context_update_namespace
             (ctxt:compilation_context) (nsctxt:namespace_ctxt) : compilation_context :=
    mkCompCtxt nsctxt
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).
         
  Definition compilation_context_update_function_env
             (ctxt : compilation_context)
             (name : string)
             (value : ergoc_function) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ((name, value)::ctxt.(compilation_context_function_env))
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition update_function_group_env
             (gname:string)
             (fname:string)
             (fn:ergoc_function)
             (fg_env:function_group_env) : function_group_env :=
    match lookup string_dec fg_env gname with
    | Some t => update_first string_dec fg_env gname ((fname,fn)::t)
    | None => (gname,((fname,fn)::nil)) :: fg_env
    end.

  Definition compilation_context_update_function_group_env
             (ctxt : compilation_context)
             (coname : string)
             (clname : string)
             (value : ergoc_function) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               (update_function_group_env coname clname value ctxt.(compilation_context_function_group_env))
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_update_global_env
             (ctxt : compilation_context)
             (name : string)
             (value : ergoc_expr) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ((name, value)::ctxt.(compilation_context_global_env))
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_update_local_env
             (ctxt : compilation_context)
             (name : string)
             (value : ergoc_expr) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ((name, value)::ctxt.(compilation_context_local_env))
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_set_local_env
             (ctxt : compilation_context)
             (new_local_env : list (string * ergoc_expr)) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               new_local_env
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_update_params_env
             (ctxt : compilation_context)
             (param : string) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               (param::ctxt.(compilation_context_params_env))
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_set_params_env
             (ctxt : compilation_context)
             (params : list string) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               params
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition set_namespace_in_compilation_context
             (ns:namespace_name)
             (ctxt:compilation_context)
    : eresult compilation_context :=
    elift
      (compilation_context_update_namespace
         ctxt)
      (new_ergo_module_namespace
         (namespace_ctxt_of_compilation_context ctxt)
         ns).

  Definition set_current_contract (ctxt:compilation_context) (cname:string) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               (Some cname)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).
  
  Definition set_current_clause (ctxt:compilation_context) (cname:string) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               (Some cname)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_update_type_ctxt
             (ctxt: compilation_context)
             (nctxt: type_context) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               nctxt
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               ctxt.(compilation_context_warnings).

  Definition compilation_context_update_type_declarations
             (ctxt: compilation_context)
             (old_decls:list laergo_type_declaration)
             (new_decls:list laergo_type_declaration)  : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               (sort_decls old_decls)
               (sort_decls new_decls)
               ctxt.(compilation_context_warnings).
  
  Definition compilation_context_add_new_type_declaration
             (ctxt: compilation_context)
             (decl:laergo_type_declaration) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               (sort_decls (ctxt.(compilation_context_new_type_decls) ++ (decl::nil)))
               ctxt.(compilation_context_warnings).

  Definition compilation_context_add_warnings
             (ctxt: compilation_context)
             (warnings:list ewarning) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               (ctxt.(compilation_context_warnings) ++ warnings).

  Definition compilation_context_reset_warnings
             (ctxt: compilation_context) : compilation_context :=
    mkCompCtxt ctxt.(compilation_context_namespace)
               ctxt.(compilation_context_function_env)
               ctxt.(compilation_context_function_group_env)
               ctxt.(compilation_context_global_env)
               ctxt.(compilation_context_local_env)
               ctxt.(compilation_context_params_env)
               ctxt.(compilation_context_current_contract)
               ctxt.(compilation_context_current_clause)
               ctxt.(compilation_context_type_ctxt)
               ctxt.(compilation_context_type_decls)
               ctxt.(compilation_context_new_type_decls)
               nil.

  Definition get_all_decls ctxt : list laergo_type_declaration :=
    sort_decls (ctxt.(compilation_context_type_decls) ++ ctxt.(compilation_context_new_type_decls)).

  Definition init_compilation_context nsctxt decls : compilation_context :=
    mkCompCtxt nsctxt nil nil nil nil nil None None empty_type_context decls nil nil.

  Definition is_abstract_class
             (ctxt: compilation_context)
             (n:string) :=
    if in_dec string_dec n ctxt.(compilation_context_namespace).(namespace_ctxt_abstract)
    then true
    else false.
  
End ErgoCompContext.
