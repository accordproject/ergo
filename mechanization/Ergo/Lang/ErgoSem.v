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
Require Import ErgoSpec.Common.Utils.EError.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoSem.
  Definition env := list (string * ErgoData.data).
  Definition mod_context := list ergo_package.

  Definition etypeerror msg : eresult ErgoData.data := efailure (EResult.TypeError msg).
  Definition variable_not_found : eresult ErgoData.data := etypeerror "variable not found"%string.

  (** Currently, this is written as a big-step semantics. There is
      some amount of duplication in rules preconditions due to error
      handling. This might benefit to be written in a pretty-big-step
      semantic style.  See [Charguéraud ESOP 2013]
      http://www.chargueraud.org/research/2012/pretty/ *)

  Inductive ergo_expr_sem : mod_context -> env -> ergo_expr -> eresult (ErgoData.data) -> Prop :=
  | sem_EVar : forall mc env v d,
      lookup equiv_dec env v = Some d ->              (**r   [Γ(v) = d] *)
      ergo_expr_sem mc env (EVar v) (esuccess d)      
  | sem_EVar_fail : forall mc env v,
      lookup equiv_dec env v = None ->
      ergo_expr_sem mc env (EVar v) variable_not_found
  | sem_EConst : forall mc env d,
      ergo_expr_sem mc env (EConst d) (esuccess d)
  | sem_EArray_nil : forall mc env,
      ergo_expr_sem mc env (EArray nil) (esuccess (ErgoData.dcoll nil))
  | sem_EArray_cons : forall mc env e1 el d1 dl,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ergo_expr_sem mc env (EArray el) (esuccess (ErgoData.dcoll dl)) ->
      ergo_expr_sem mc env (EArray (e1::el)) (esuccess (ErgoData.dcoll (d1::dl)))
  | sem_EArray_cons_fail : forall mc env e1 el err,
      ergo_expr_sem mc env e1 (efailure err) ->
      ergo_expr_sem mc env (EArray (e1::el)) (efailure err)
  | sem_EUnaryOp : forall uop mc env e1 h d1 d2,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ErgoOps.Unary.eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
      ergo_expr_sem mc env (EUnaryOp uop e1) (esuccess d2)
  | sem_EUnaryOp_wrongtype : forall uop mc env h e1 d1,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ErgoOps.Unary.eval h uop d1 = None ->
      ergo_expr_sem mc env (EUnaryOp uop e1) (etypeerror "UnaryOp")
  | sem_EBinnaryOp : forall bop mc env e1 e2 h d1 d2 d3,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ergo_expr_sem mc env e2 (esuccess d2) ->
      ErgoOps.Binary.eval h bop d1 d2 = Some d3 ->
      ergo_expr_sem mc env (EBinaryOp bop e1 e2) (esuccess d2)
  | sem_EBinaryOp_wrongtype : forall bop mc env e1 e2 h d1 d2,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ergo_expr_sem mc env e2 (esuccess d2) ->
      ErgoOps.Binary.eval h bop d1 d2 = None ->
      ergo_expr_sem mc env (EBinaryOp bop e1 e2) (etypeerror "BinaryOp")
  | sem_EIf_true : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool true)) ->
      ergo_expr_sem mc env e2 (esuccess d) ->
      ergo_expr_sem mc env (EIf e1 e2 e3) (esuccess d)
  | sem_EIf_false : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool false)) ->
      ergo_expr_sem mc env e3 (esuccess d) ->
      ergo_expr_sem mc env (EIf e1 e2 e3) (esuccess d)
  | sem_EIf_fail : forall mc env e1 e2 e3 err,
      ergo_expr_sem mc env e1 (efailure err) ->
      ergo_expr_sem mc env (EIf e1 e2 e3) (efailure err)
  | sem_EIf_true_fail : forall mc env e1 e2 e3 err,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool true)) ->
      ergo_expr_sem mc env e2 (efailure err) ->
      ergo_expr_sem mc env (EIf e1 e2 e3) (efailure err)
  | sem_EIf_false_fail : forall mc env e1 e2 e3 err,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool false)) ->
      ergo_expr_sem mc env e3 (efailure err) ->
      ergo_expr_sem mc env (EIf e1 e2 e3) (efailure err)
  | sem_EEnforce_true : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool true)) ->
      ergo_expr_sem mc env e3 (esuccess d) ->
      ergo_expr_sem mc env (EEnforce e1 e2 e3) (esuccess d)
  | sem_EEnforce_false_some : forall mc env e1 e2 e3 d,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool false)) ->
      ergo_expr_sem mc env e2 (esuccess d) ->
      ergo_expr_sem mc env (EEnforce e1 (Some e2) e3) (esuccess d)
  | sem_EEnforce_false_none : forall mc env e1 e3,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool false)) ->
      ergo_expr_sem mc env (EEnforce e1 None e3) (efailure enforce_error)
  | sem_EEnforce_fail : forall mc env e1 opte2 e3 err,
      ergo_expr_sem mc env e1 (efailure err) ->
      ergo_expr_sem mc env (EEnforce e1 opte2 e3) (efailure err)
  | sem_EEnforce_fail_left : forall mc env e1 opte2 e3 err,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool true)) ->
      ergo_expr_sem mc env e3 (efailure err) ->
      ergo_expr_sem mc env (EEnforce e1 opte2 e3) (efailure err)
  | sem_EEnforce_fail_right : forall mc env e1 e2 e3 err,
      ergo_expr_sem mc env e1 (esuccess (ErgoData.dbool false)) ->
      ergo_expr_sem mc env e3 (efailure err) ->
      ergo_expr_sem mc env (EEnforce e1 (Some e2) e3) (efailure err)
  | sem_ELet : forall mc env v e1 e2 d1 d2,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      ergo_expr_sem mc ((v,d1)::env) e2 (esuccess d2) ->
      ergo_expr_sem mc env (ELet v None e1 e2) (esuccess d2)
  | sem_ELet_typed : forall mc env v t e1 e2 d1 d2,
      ergo_expr_sem mc env e1 (esuccess d1) ->
      (** instance_of d1 t1 = true -> *) (* XXX TBD!! *)
      ergo_expr_sem mc ((v,d1)::env) e2 (esuccess d2) ->
      ergo_expr_sem mc env (ELet v (Some t) e1 e2) (esuccess d2)
  .

End ErgoSem.

