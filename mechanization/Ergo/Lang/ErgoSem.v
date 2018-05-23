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

(** * Semantics *)

Require Import String.
Require Import List.
Require Import EquivDec.

Require Import Qcert.Utils.Utils.

Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoSem.
  Record env :=
    mkDynEnv
        { env_this_contract : ErgoData.data;
          env_this_clause : ErgoData.data;
          env_this_state : ErgoData.data;
          env_this_emit : list ErgoData.data;
          env_variables : list (string * ErgoData.data); }.

  Definition env_add_variable env v d :=
    mkDynEnv
      env.(env_this_contract)
      env.(env_this_clause)
      env.(env_this_state)
      env.(env_this_emit)
      ((v,d)::env.(env_variables)).
  
  Definition mod_context := list ergo_package.

  (** Currently, this is written as a big-step semantics. There is
      some amount of duplication in rules preconditions due to error
      handling. This might benefit to be written in a pretty-big-step
      semantic style.  See [Charguéraud ESOP 2013]
      http://www.chargueraud.org/research/2012/pretty/ *)

  Inductive ergo_expr_sem : mod_context -> env -> ergo_expr -> ErgoData.data -> Prop :=
  | sem_EThisContract : forall mc env,
      ergo_expr_sem mc env EThisContract (env.(env_this_contract))
  | sem_EThisClause : forall mc env,
      ergo_expr_sem mc env EThisClause (env.(env_this_clause))
  | sem_EThisState : forall mc env,
      ergo_expr_sem mc env EThisState (env.(env_this_state))
  | sem_EVar : forall mc env v d,
      lookup equiv_dec env.(env_variables) v = Some d ->              (**r   [Γ(v) = d] *)
      ergo_expr_sem mc env (EVar v) d      
  | sem_EConst : forall mc env d,
      ergo_expr_sem mc env (EConst d) d
  | sem_EArray_nil : forall mc env,
      ergo_expr_sem mc env (EArray nil) (ErgoData.dcoll nil)
  | sem_EArray_cons : forall mc env e1 el d1 dl,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env (EArray el) (ErgoData.dcoll dl) ->
      ergo_expr_sem mc env (EArray (e1::el)) (ErgoData.dcoll (d1::dl))
  | sem_EUnaryOp : forall uop mc env e1 h d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      ErgoOps.Unary.eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
      ergo_expr_sem mc env (EUnaryOp uop e1) d2
  | sem_EBinnaryOp : forall bop mc env e1 e2 h d1 d2 d3,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env e2 d2 ->
      ErgoOps.Binary.eval h bop d1 d2 = Some d3 ->
      ergo_expr_sem mc env (EBinaryOp bop e1 e2) d2
  | sem_EIf_true : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (ErgoData.dbool true) ->
      ergo_expr_sem mc env e2 d ->
      ergo_expr_sem mc env (EIf e1 e2 e3) d
  | sem_EIf_false : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (ErgoData.dbool false) ->
      ergo_expr_sem mc env e3 d ->
      ergo_expr_sem mc env (EIf e1 e2 e3) d
  | sem_ELet : forall mc env v e1 e2 d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc (env_add_variable env v d1) e2 d2 ->
      ergo_expr_sem mc env (ELet v None e1 e2) d2
  | sem_ELet_typed : forall mc env v t e1 e2 d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      (** instance_of d1 t1 = true -> *) (* XXX TBD!! *)
      ergo_expr_sem mc (env_add_variable env v d1) e2 d2 ->
      ergo_expr_sem mc env (ELet v (Some t) e1 e2) d2
  | sem_ERecord_nil : forall mc env,
      ergo_expr_sem mc env (ERecord nil) (ErgoData.drec nil)
  | sem_ERecord_cons : forall mc env v e1 el d1 rl rl',
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env (ERecord el) (ErgoData.drec rl) ->
      rec_sort ((v,d1)::rl) = rl' -> (* Ensures the record is sorted for normalization *)
      ergo_expr_sem mc env (ERecord ((v,e1)::el)) (ErgoData.drec rl')
  .

End ErgoSem.

