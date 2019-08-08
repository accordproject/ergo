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
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCEvalContext.

  Record eval_context :=
    mkEvalContext
      { eval_context_global_env : list (string * ergo_data);
        eval_context_local_env : list (string * ergo_data);
      }.

  Definition eval_context_update_global_env
             (ctxt : eval_context)
             (name : string)
             (value : ergo_data) : eval_context :=
    mkEvalContext ((name, value)::ctxt.(eval_context_global_env))
                  ctxt.(eval_context_local_env).

  Definition eval_context_update_local_env
             (ctxt : eval_context)
             (name : string)
             (value : ergo_data) : eval_context :=
    mkEvalContext ctxt.(eval_context_global_env)
                  ((name, value)::ctxt.(eval_context_local_env)).

  Definition eval_context_set_local_env
             (ctxt : eval_context)
             (new_local_env : list (string * ergo_data)) : eval_context :=
    mkEvalContext ctxt.(eval_context_global_env)
                  new_local_env.

  Definition empty_eval_context :=
    mkEvalContext  ((markdown_options,
                     dbrand (default_markdown_options::nil)
                            (drec (("wrapVariables"%string, dbool false)
                                     ::("template"%string, dbool false)
                                     ::nil)))
                      ::(current_time, dforeign (ErgoEnhancedModel.enhanceddateTime ErgoEnhancedModel.enhanceddateTime_now))
                      ::(this_contract, dunit)
                      ::(this_state, dunit)
                      ::(this_emit, dcoll nil)
                      ::nil)
                   (nil).

End ErgoCEvalContext.

