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
Require Import ErgoSpec.Common.Names.

Section ErgoCTypecheckContext.
  Context {br : brand_relation}.
  Import ErgoCType.

  Record type_context :=
    mkEvalContext
      { type_context_global_env : list (string * ergoc_type);
        type_context_local_env : list (string * ergoc_type);
      }.

  Definition type_context_update_global_env
             (ctxt : type_context)
             (name : string)
             (value : ergoc_type) : type_context :=
    mkEvalContext ((name, value)::ctxt.(type_context_global_env))
                  ctxt.(type_context_local_env).

  Definition type_context_update_local_env
             (ctxt : type_context)
             (name : string)
             (value : ergoc_type) : type_context :=
    mkEvalContext ctxt.(type_context_global_env)
                  ((name, value)::ctxt.(type_context_local_env)).

  Definition type_context_set_local_env
             (ctxt : type_context)
             (new_local_env : list (string * ergoc_type)) : type_context :=
    mkEvalContext ctxt.(type_context_global_env)
                  new_local_env.

  Definition empty_type_context :=
    mkEvalContext  ((markdown_options,tbrand (default_markdown_options::nil))
                      ::(current_time,tdateTime)
                      ::(this_contract,tunit)
                      ::(this_state,tunit)
                      ::(this_emit,tcoll tbottom)
                      ::nil)
                   (nil).
  
End ErgoCTypecheckContext.

