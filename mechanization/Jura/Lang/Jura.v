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

(** Jura is a language for expressing contract logic. *)

(** * Abstract Syntax *)

Require Import String.
Require Import Qcert.Common.CommonRuntime.
Require Import Jura.Common.CTO.CTO.
Require Import Jura.Jura.Lang.JuraBase.

Section Jura.
  Context {fruntime:foreign_runtime}.

  Section Syntax.

    Inductive match_case_kind :=
    | CaseValue : data -> match_case_kind    (**r match against value *)
    | CaseType : string -> match_case_kind   (**r match against type *)
    .

    Definition match_case :=
      (option string * match_case_kind)%type. (**r optional variable and case kind *)

    (** Expression *)
    Inductive jura_expr :=
    | JVar : string -> jura_expr (**r Local variable access *)
    | JConst : data -> jura_expr (**r Constant *)
    | JArray : list jura_expr -> jura_expr (**r Array constructor *) 
    | JUnaryOp : unary_op -> jura_expr -> jura_expr (**r Unary operator *)
    | JBinaryOp : binary_op -> jura_expr -> jura_expr -> jura_expr (**r Binary operator *)
    | JIf : jura_expr -> jura_expr -> jura_expr -> jura_expr (**r Conditional *)
    | JEnsure : jura_expr -> option jura_expr -> jura_expr -> jura_expr (**r Ensure *)
    | JDefineVar : string -> option cto_type -> jura_expr -> jura_expr -> jura_expr (**r Local variable binding *)
    | JNew : class_ref -> list (string * jura_expr) -> jura_expr (**r Create a new concept/object *)
    | JThrow : class_ref -> list (string * jura_expr) -> jura_expr (**r Create a new concept/object *)
    | JFunCall : string -> list jura_expr -> jura_expr (**r function call *)
    | JMatch : jura_expr -> list (match_case * jura_expr) -> jura_expr -> jura_expr (**r match-case *)
    | JFor : string -> jura_expr -> option jura_expr -> jura_expr -> jura_expr (**r for loop with optional where *)
    .

    (** Clause *)
    Definition jura_clause := @clause jura_expr.

    (** Function *)
    Definition jura_func := @func jura_expr.

    (** Declaration *)
    Definition jura_declaration := @declaration jura_expr.

    (** Contract *)
    Definition jura_contract := @contract jura_expr.

    (** Statement *)
    Definition jura_stmt := @stmt jura_expr.

    (** Package. *)
    Definition jura_package := @package jura_expr.

  End Syntax.

  Section Semantics.
    Require Import EquivDec.
    Require Import Qcert.Utils.Utils.
    Require Import Jura.Utils.JResult.
    Require Import Jura.Utils.JError.

    Definition env := list (string * data).
    Definition mod_context := list jura_package.
    Definition jtypeerror msg : jresult data := jfailure (TypeError msg).
    Definition variable_not_found : jresult data := jtypeerror "variable not found"%string.

    Context (h:brand_relation_t).

    Inductive jura_expr_sem : mod_context -> env -> jura_expr -> jresult data -> Prop :=
    | sem_JVar : forall mc env v d,
        lookup equiv_dec env v = Some d ->              (**r   [Γ(v) = d] *)
        jura_expr_sem mc env (JVar v) (jsuccess d)      
    | sem_JVar_fail : forall mc env v,
        lookup equiv_dec env v = None ->
        jura_expr_sem mc env (JVar v) variable_not_found
    | sem_JConst : forall mc env d,
        jura_expr_sem mc env (JConst d) (jsuccess d)
    | sem_JArray_nil : forall mc env,
        jura_expr_sem mc env (JArray nil) (jsuccess (dcoll nil))
    | sem_JArray_cons : forall mc env e1 el d1 dl,
        jura_expr_sem mc env e1 (jsuccess d1) ->
        jura_expr_sem mc env (JArray el) (jsuccess (dcoll dl)) ->
        jura_expr_sem mc env (JArray (e1::el)) (jsuccess (dcoll (d1::dl)))
    | sem_JArray_cons_fail : forall mc env e1 el err,
        jura_expr_sem mc env e1 (jfailure err) ->
        jura_expr_sem mc env (JArray (e1::el)) (jfailure err)
    | sem_JUnaryOp : forall uop mc env e1 d1 d2,
        jura_expr_sem mc env e1 (jsuccess d1) ->
        unary_op_eval h uop d1 = Some d2 ->             (**r ∧ [⊞ d₁ = d₂] *)
        jura_expr_sem mc env (JUnaryOp uop e1) (jsuccess d2)
    | sem_JUnaryOp_wrongtype : forall uop mc env e1 d1,
        jura_expr_sem mc env e1 (jsuccess d1) ->
        unary_op_eval h uop d1 = None ->
        jura_expr_sem mc env (JUnaryOp uop e1) (jtypeerror "UnaryOp")
    | sem_JUnaryOp_fail : forall uop mc env e1 err,
        jura_expr_sem mc env e1 (jfailure err) ->
        jura_expr_sem mc env (JUnaryOp uop e1) (jfailure err)
    | sem_JBinnaryOp : forall bop mc env e1 e2 d1 d2 d3,
        jura_expr_sem mc env e1 (jsuccess d1) ->
        jura_expr_sem mc env e2 (jsuccess d2) ->
        binary_op_eval h bop d1 d2 = Some d3 ->
        jura_expr_sem mc env (JBinaryOp bop e1 e2) (jsuccess d2)
    | sem_JBinaryOp_wrongtype : forall bop mc env e1 e2 d1 d2,
        jura_expr_sem mc env e1 (jsuccess d1) ->
        jura_expr_sem mc env e2 (jsuccess d2) ->
        binary_op_eval h bop d1 d2 = None ->
        jura_expr_sem mc env (JBinaryOp bop e1 e2) (jtypeerror "BinaryOp")
    | sem_JUnaryOp_fail_left : forall bop mc env e1 e2 err,
        jura_expr_sem mc env e1 (jfailure err) ->
        jura_expr_sem mc env (JBinaryOp bop e1 e2) (jfailure err)
    | sem_JUnaryOp_fail_right : forall bop mc env e1 e2 d1 err,
        jura_expr_sem mc env e1 (jsuccess d1) -> (** XXX Not sure we need/want this precondition *)
        jura_expr_sem mc env e2 (jfailure err) ->
        jura_expr_sem mc env (JBinaryOp bop e1 e2) (jfailure err)
    | sem_JIf_true : forall mc env e1 e2 e3 d,
        jura_expr_sem mc env e1 (jsuccess (dbool true)) ->
        jura_expr_sem mc env e2 (jsuccess d) ->
        jura_expr_sem mc env (JIf e1 e2 e3) (jsuccess d)
    | sem_JIf_false : forall mc env e1 e2 e3 d,
        jura_expr_sem mc env e1 (jsuccess (dbool false)) ->
        jura_expr_sem mc env e3 (jsuccess d) ->
        jura_expr_sem mc env (JIf e1 e2 e3) (jsuccess d)
    | sem_JIf_fail : forall mc env e1 e2 e3 err,
        jura_expr_sem mc env e1 (jfailure err) ->
        jura_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JIf_true_fail : forall mc env e1 e2 e3 err,
        jura_expr_sem mc env e1 (jsuccess (dbool true)) ->
        jura_expr_sem mc env e2 (jfailure err) ->
        jura_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JIf_false_fail : forall mc env e1 e2 e3 err,
        jura_expr_sem mc env e1 (jsuccess (dbool false)) ->
        jura_expr_sem mc env e3 (jfailure err) ->
        jura_expr_sem mc env (JIf e1 e2 e3) (jfailure err)
    | sem_JEnsure_true : forall mc env e1 e2 e3 d,
        jura_expr_sem mc env e1 (jsuccess (dbool true)) ->
        jura_expr_sem mc env e3 (jsuccess d) ->
        jura_expr_sem mc env (JEnsure e1 e2 e3) (jsuccess d)
    | sem_JEnsure_false_some : forall mc env e1 e2 e3 d,
        jura_expr_sem mc env e1 (jsuccess (dbool false)) ->
        jura_expr_sem mc env e2 (jsuccess d) ->
        jura_expr_sem mc env (JEnsure e1 (Some e2) e3) (jsuccess d)
    | sem_JEnsure_false_none : forall mc env e1 e3,
        jura_expr_sem mc env e1 (jsuccess (dbool false)) ->
        jura_expr_sem mc env (JEnsure e1 None e3) (jfailure ensure_error)
    | sem_JEnsure_fail : forall mc env e1 opte2 e3 err,
        jura_expr_sem mc env e1 (jfailure err) ->
        jura_expr_sem mc env (JEnsure e1 opte2 e3) (jfailure err)
    | sem_JEnsure_fail_left : forall mc env e1 opte2 e3 err,
        jura_expr_sem mc env e1 (jsuccess (dbool true)) ->
        jura_expr_sem mc env e3 (jfailure err) ->
        jura_expr_sem mc env (JEnsure e1 opte2 e3) (jfailure err)
    | sem_JEnsure_fail_right : forall mc env e1 e2 e3 err,
        jura_expr_sem mc env e1 (jsuccess (dbool false)) ->
        jura_expr_sem mc env e3 (jfailure err) ->
        jura_expr_sem mc env (JEnsure e1 (Some e2) e3) (jfailure err)
    .
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End Jura.

