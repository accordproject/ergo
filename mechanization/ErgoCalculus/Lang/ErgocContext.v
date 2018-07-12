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
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoCalculus.

Section ErgocContext.

Definition ergo_data := ErgoData.data.
  Record ergo_context :=
    mkContext
      { ctx_function_env : list (string * ergoc_function);
        ctx_clause_env : list (string * laergo_clause);
        ctx_contract_env : list (string * laergo_contract);
        ctx_global_env : list (string * ergo_data);
        ctx_local_env : list (string * ergo_data);
        ctx_this_clause : ergo_data;
        ctx_this_contract : ergo_data;
        ctx_this_state : ergo_data;
        ctx_this_emit : ergo_data;
        }.

  Definition ergo_ctx_update_function_env (ctx : ergo_context) (name : string) (value : ergoc_function) : ergo_context :=
    mkContext ((name, value)::ctx.(ctx_function_env))
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              ctx.(ctx_local_env)
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_update_global_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              ((name, value)::ctx.(ctx_global_env))
              (ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_update_local_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              ((name, value)::ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_set_local_env (ctx : ergo_context) (new_local_env : list (string * ergo_data)) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              new_local_env
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

End ErgocContext.
