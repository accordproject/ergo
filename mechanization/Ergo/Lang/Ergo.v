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
Require Import Ergo.Common.Utils.JNames.
Require Import Ergo.Common.CTO.CTO.
Require Import Ergo.Ergo.Lang.ErgoBase.
Require Import Ergo.Backend.ErgoBackend.

Section Ergo.
  Section Syntax.

    Inductive match_case_kind :=
    | CaseValue : ErgoData.data -> match_case_kind    (**r match against value *)
    | CaseType : string -> match_case_kind   (**r match against type *)
    .

    Definition match_case :=
      (option string * match_case_kind)%type. (**r optional variable and case kind *)

    (** Expression *)
    Inductive ergo_expr :=
    | JThisContract : ergo_expr (**r this contract *)
    | JThisClause : ergo_expr (**r this clause *)
    | JThisState : ergo_expr (**r this state *)
    | JVar : string -> ergo_expr (**r variable *)
    | JConst : ErgoData.data -> ergo_expr (**r constant *)
    | JArray : list ergo_expr -> ergo_expr (**r array constructor *) 
    | JUnaryOp : ErgoOps.Unary.op -> ergo_expr -> ergo_expr (**r unary operator *)
    | JBinaryOp : ErgoOps.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr (**r binary operator *)
    | JIf : ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr (**r conditional *)
    | JEnforce : ergo_expr -> option ergo_expr -> ergo_expr -> ergo_expr (**r enforce *)
    | JLet : string -> option cto_type -> ergo_expr -> ergo_expr -> ergo_expr (**r local variable binding *)
    | JRecord : list (string * ergo_expr) -> ergo_expr (**r create a new record *)
    | JNew : class_ref -> list (string * ergo_expr) -> ergo_expr (**r create a new concept/object *)
    | JThrow : class_ref -> list (string * ergo_expr) -> ergo_expr (**r create a new concept/object *)
    | JFunCall : string -> list ergo_expr -> ergo_expr (**r function call *)
    | JMatch : ergo_expr -> list (match_case * ergo_expr) -> ergo_expr -> ergo_expr (**r match-case *)
    | JFor : string -> ergo_expr -> option ergo_expr -> ergo_expr -> ergo_expr (**r for loop with optional where *)
    .

    (** Clause *)
    Definition ergo_clause := @clause ergo_expr.

    (** Function *)
    Definition ergo_func := @func ergo_expr.

    (** Declaration *)
    Definition ergo_declaration := @declaration ergo_expr.

    (** Contract *)
    Definition ergo_contract := @contract ergo_expr.

    (** Statement *)
    Definition ergo_stmt := @stmt ergo_expr.

    (** Package. *)
    Definition ergo_package := @package ergo_expr.

  End Syntax.

  Section Semantics.
    Require Import List.
    Require Import EquivDec.
    Require Import Qcert.Utils.Utils.
    Require Import Ergo.Common.Utils.JResult.
    Require Import Ergo.Common.Utils.JError.

    Definition env := list (string * ErgoData.data).
    Definition mod_context := list ergo_package.
    Definition jtypeerror msg : jresult ErgoData.data := jfailure (TypeError msg).
    Definition variable_not_found : jresult ErgoData.data := jtypeerror "variable not found"%string.

    (** Currently, this is written as a big-step semantics. There is
       some amount of duplication in rules preconditions due to error
       handling. This might benefit to be written in a pretty-big-step
       semantic style.  See [Charguéraud ESOP 2013]
       http://www.chargueraud.org/research/2012/pretty/ *)

    Inductive ergo_expr_sem : mod_context -> env -> ergo_expr -> jresult (ErgoData.data) -> Prop :=
    | sem_JVar : forall mc env v d,
        lookup equiv_dec env v = Some d ->              (**r   [Γ(v) = d] *)
        ergo_expr_sem mc env (JVar v) (jsuccess d)      
    | sem_JVar_fail : forall mc env v,
        lookup equiv_dec env v = None ->
        ergo_expr_sem mc env (JVar v) variable_not_found
    | sem_JConst : forall mc env d,
        ergo_expr_sem mc env (JConst d) (jsuccess d)
    | sem_JArray_nil : forall mc env,
        ergo_expr_sem mc env (JArray nil) (jsuccess (ErgoData.dcoll nil))
    | sem_JArray_cons : forall mc env e1 el d1 dl,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ergo_expr_sem mc env (JArray el) (jsuccess (ErgoData.dcoll dl)) ->
        ergo_expr_sem mc env (JArray (e1::el)) (jsuccess (ErgoData.dcoll (d1::dl)))
    | sem_JArray_cons_fail : forall mc env e1 el err,
        ergo_expr_sem mc env e1 (jfailure err) ->
        ergo_expr_sem mc env (JArray (e1::el)) (jfailure err)
    | sem_JUnaryOp : forall uop mc env e1 h d1 d2,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ErgoOps.Unary.eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
        ergo_expr_sem mc env (JUnaryOp uop e1) (jsuccess d2)
    | sem_JUnaryOp_wrongtype : forall uop mc env h e1 d1,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ErgoOps.Unary.eval h uop d1 = None ->
        ergo_expr_sem mc env (JUnaryOp uop e1) (jtypeerror "UnaryOp")
    | sem_JBinnaryOp : forall bop mc env e1 e2 h d1 d2 d3,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ergo_expr_sem mc env e2 (jsuccess d2) ->
        ErgoOps.Binary.eval h bop d1 d2 = Some d3 ->
        ergo_expr_sem mc env (JBinaryOp bop e1 e2) (jsuccess d2)
    | sem_JBinaryOp_wrongtype : forall bop mc env e1 e2 h d1 d2,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ergo_expr_sem mc env e2 (jsuccess d2) ->
        ErgoOps.Binary.eval h bop d1 d2 = None ->
        ergo_expr_sem mc env (JBinaryOp bop e1 e2) (jtypeerror "BinaryOp")
    | sem_JIf_true : forall mc env e1 e2 e3 d,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool true)) ->
        ergo_expr_sem mc env e2 (jsuccess d) ->
        ergo_expr_sem mc env (JIf e1 e2 e3) (jsuccess d)
    | sem_JIf_false : forall mc env e1 e2 e3 d,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool false)) ->
        ergo_expr_sem mc env e3 (jsuccess d) ->
        ergo_expr_sem mc env (JIf e1 e2 e3) (jsuccess d)
    | sem_JIf_fail : forall mc env e1 e2 e3 err,
        ergo_expr_sem mc env e1 (jfailure err) ->
        ergo_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JIf_true_fail : forall mc env e1 e2 e3 err,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool true)) ->
        ergo_expr_sem mc env e2 (jfailure err) ->
        ergo_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JIf_false_fail : forall mc env e1 e2 e3 err,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool false)) ->
        ergo_expr_sem mc env e3 (jfailure err) ->
        ergo_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JEnforce_true : forall mc env e1 e2 e3 d,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool true)) ->
        ergo_expr_sem mc env e3 (jsuccess d) ->
        ergo_expr_sem mc env (JEnforce e1 e2 e3) (jsuccess d)
    | sem_JEnforce_false_some : forall mc env e1 e2 e3 d,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool false)) ->
        ergo_expr_sem mc env e2 (jsuccess d) ->
        ergo_expr_sem mc env (JEnforce e1 (Some e2) e3) (jsuccess d)
    | sem_JEnforce_false_none : forall mc env e1 e3,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool false)) ->
        ergo_expr_sem mc env (JEnforce e1 None e3) (jfailure enforce_error)
    | sem_JEnforce_fail : forall mc env e1 opte2 e3 err,
        ergo_expr_sem mc env e1 (jfailure err) ->
        ergo_expr_sem mc env (JEnforce e1 opte2 e3) (jfailure err)
    | sem_JEnforce_fail_left : forall mc env e1 opte2 e3 err,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool true)) ->
        ergo_expr_sem mc env e3 (jfailure err) ->
        ergo_expr_sem mc env (JEnforce e1 opte2 e3) (jfailure err)
    | sem_JEnforce_fail_right : forall mc env e1 e2 e3 err,
        ergo_expr_sem mc env e1 (jsuccess (ErgoData.dbool false)) ->
        ergo_expr_sem mc env e3 (jfailure err) ->
        ergo_expr_sem mc env (JEnforce e1 (Some e2) e3) (jfailure err)
    | sem_JLet : forall mc env v e1 e2 d1 d2,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        ergo_expr_sem mc ((v,d1)::env) e2 (jsuccess d2) ->
        ergo_expr_sem mc env (JLet v None e1 e2) (jsuccess d2)
    | sem_JLet_typed : forall mc env v t e1 e2 d1 d2,
        ergo_expr_sem mc env e1 (jsuccess d1) ->
        (** instance_of d1 t1 = true -> *) (* XXX TBD!! *)
        ergo_expr_sem mc ((v,d1)::env) e2 (jsuccess d2) ->
        ergo_expr_sem mc env (JLet v (Some t) e1 e2) (jsuccess d2)
    .
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End Ergo.

