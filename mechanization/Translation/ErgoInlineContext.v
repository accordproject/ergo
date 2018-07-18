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
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCInlineContext.

  Record inline_context :=
    mkInlineContext
      { inline_context_function_env : list (string * ergoc_function);
        inline_context_global_env : list (string * ergoc_expr);
        inline_context_local_env : list (string * ergoc_expr);
      }.

  Definition inline_context_update_function_env
             (ctxt : inline_context)
             (name : string)
             (value : ergoc_function) : inline_context :=
    mkInlineContext ((name, value)::ctxt.(inline_context_function_env))
                  ctxt.(inline_context_global_env)
                  ctxt.(inline_context_local_env).

  Definition inline_context_update_global_env
             (ctxt : inline_context)
             (name : string)
             (value : ergoc_expr) : inline_context :=
    mkInlineContext ctxt.(inline_context_function_env)
                  ((name, value)::ctxt.(inline_context_global_env))
                  ctxt.(inline_context_local_env).

  Definition inline_context_update_local_env
             (ctxt : inline_context)
             (name : string)
             (value : ergoc_expr) : inline_context :=
    mkInlineContext ctxt.(inline_context_function_env)
                  ctxt.(inline_context_global_env)
                  ((name, value)::ctxt.(inline_context_local_env)).

  Definition inline_context_set_local_env
             (ctxt : inline_context)
             (new_local_env : list (string * ergoc_expr)) : inline_context :=
    mkInlineContext ctxt.(inline_context_function_env)
                  ctxt.(inline_context_global_env)
                  new_local_env.

  Definition empty_inline_context :=
    mkInlineContext nil nil nil.
  
End ErgoCInlineContext.
