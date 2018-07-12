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
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgocEvalContext.

  Record eval_context :=
    mkEvalContext
      { ctx_function_env : list (string * ergoc_function);
        ctx_global_env : list (string * ergo_data);
        ctx_local_env : list (string * ergo_data);
      }.

  Definition ergo_ctx_update_function_env
             (ctx : eval_context)
             (name : string)
             (value : ergoc_function) : eval_context :=
    mkEvalContext ((name, value)::ctx.(ctx_function_env))
                  ctx.(ctx_global_env)
                  ctx.(ctx_local_env).

  Definition ergo_ctx_update_global_env
             (ctx : eval_context)
             (name : string)
             (value : ergo_data) : eval_context :=
    mkEvalContext ctx.(ctx_function_env)
                  ((name, value)::ctx.(ctx_global_env))
                  ctx.(ctx_local_env).

  Definition ergo_ctx_update_local_env
             (ctx : eval_context)
             (name : string)
             (value : ergo_data) : eval_context :=
    mkEvalContext ctx.(ctx_function_env)
                  ctx.(ctx_global_env)
                  ((name, value)::ctx.(ctx_local_env)).

  Definition ergo_ctx_set_local_env
             (ctx : eval_context)
             (new_local_env : list (string * ergo_data)) : eval_context :=
    mkEvalContext ctx.(ctx_function_env)
                  ctx.(ctx_global_env)
                  new_local_env.

  Definition ergo_empty_context :=
    mkEvalContext nil nil
                  (("contract"%string, dunit)
                     ::("state"%string, dunit)
                     ::("emit"%string, dcoll nil)
                     ::("now"%string, dunit)
                     ::nil).
  
End ErgocEvalContext.

