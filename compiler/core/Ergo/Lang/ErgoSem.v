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

Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoSem.
  Record env :=
    mkDynEnv
        { env_this_contract : data;
          env_this_clause : data;
          env_this_state : data;
          env_this_emit : list data;
          env_variables : list (string * data); }.

  Definition env_add_variable env v d :=
    mkDynEnv
      env.(env_this_contract)
      env.(env_this_clause)
      env.(env_this_state)
      env.(env_this_emit)
      ((v,d)::env.(env_variables)).
  
  Definition module_context := list laergo_module.

  (** Currently, this is written as a big-step semantics. There is
      some amount of duplication in rules preconditions due to error
      handling. This might benefit to be written in a pretty-big-step
      semantic style.  See [Charguéraud ESOP 2013]
      http://www.chargueraud.org/research/2012/pretty/ *)

  Inductive ergo_expr_sem : module_context -> env -> laergo_expr -> data -> Prop :=
  | sem_EThisContract : forall a mc env,
      ergo_expr_sem mc env (EThisContract a) (env.(env_this_contract))
  | sem_EThisClause : forall a mc env,
      ergo_expr_sem mc env (EThisClause a) (env.(env_this_clause))
  | sem_EThisState : forall a mc env,
      ergo_expr_sem mc env (EThisState a) (env.(env_this_state))
  | sem_EVar : forall a mc env v d,
      lookup equiv_dec env.(env_variables) v = Some d ->              (**r   [Γ(v) = d] *)
      ergo_expr_sem mc env (EVar a v) d      
  | sem_EConst : forall a mc env d,
      ergo_expr_sem mc env (EConst a d) d
  | sem_EArray_nil : forall a mc env,
      ergo_expr_sem mc env (EArray a nil) (dcoll nil)
  | sem_EArray_cons : forall a1 a2 mc env e1 el d1 dl,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env (EArray a1 el) (dcoll dl) ->
      ergo_expr_sem mc env (EArray a2 (e1::el)) (dcoll (d1::dl))
  | sem_EUnaryBuiltin : forall a uop mc env e1 h d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      QcertOps.Unary.eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
      ergo_expr_sem mc env (EUnaryBuiltin a uop e1) d2
  | sem_EBinaryBuiltin : forall a bop mc env e1 e2 h d1 d2 d3,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env e2 d2 ->
      QcertOps.Binary.eval h bop d1 d2 = Some d3 ->
      ergo_expr_sem mc env (EBinaryBuiltin a bop e1 e2) d2
  | sem_EIf_true : forall a mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (dbool true) ->
      ergo_expr_sem mc env e2 d ->
      ergo_expr_sem mc env (EIf a e1 e2 e3) d
  | sem_EIf_false : forall a mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (dbool false) ->
      ergo_expr_sem mc env e3 d ->
      ergo_expr_sem mc env (EIf a e1 e2 e3) d
  | sem_ELet : forall a mc env v e1 e2 d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc (env_add_variable env v d1) e2 d2 ->
      ergo_expr_sem mc env (ELet a v None e1 e2) d2
  | sem_ELet_typed : forall a mc env v t e1 e2 d1 d2,
      ergo_expr_sem mc env e1 d1 ->
      (** instance_of d1 t1 = true -> *) (* XXX TBD!! *)
      ergo_expr_sem mc (env_add_variable env v d1) e2 d2 ->
      ergo_expr_sem mc env (ELet a v (Some t) e1 e2) d2
  | sem_ERecord_nil : forall a mc env,
      ergo_expr_sem mc env (ERecord a nil) (drec nil)
  | sem_ERecord_cons : forall a1 a2 mc env v e1 el d1 rl rl',
      ergo_expr_sem mc env e1 d1 ->
      ergo_expr_sem mc env (ERecord a1 el) (drec rl) ->
      rec_sort ((v,d1)::rl) = rl' -> (* Ensures the record is sorted for normalization *)
      ergo_expr_sem mc env (ERecord a2 ((v,e1)::el)) (drec rl').

End ErgoSem.

