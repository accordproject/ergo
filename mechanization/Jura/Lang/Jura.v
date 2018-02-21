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
Require Import JuraBase.

Section Jura.
  Context {fruntime:foreign_runtime}.

  Section Syntax.

    Inductive switch_case_kind :=
    | CaseValue : data -> switch_case_kind    (**r match against value *)
    | CaseType : string -> switch_case_kind   (**r match against type *)
    .

    Definition switch_case :=
      (option string * switch_case_kind)%type. (**r optional variable and case kind *)

    (** Expression *)
    Inductive jura_expr :=
    | JVar : string -> jura_expr (**r Local variable access *)
    | JConst : data -> jura_expr (**r Constant *)
    | JArray : list jura_expr -> jura_expr (**r Array constructor *) 
    | JUnaryOp : unary_op -> jura_expr -> jura_expr (**r Unary operator *)
    | JBinaryOp : binary_op -> jura_expr -> jura_expr -> jura_expr (**r Binary operator *)
    | JIf : jura_expr -> jura_expr -> jura_expr -> jura_expr (**r Conditional *)
    | JGuard : jura_expr -> jura_expr -> jura_expr -> jura_expr (**r Guard *)
    | JLet : string -> jura_expr -> jura_expr -> jura_expr (**r Local variable binding *)
    | JNew : class_ref -> list (string * jura_expr) -> jura_expr (**r Create a new concept/object *)
    | JThrow : class_ref -> list (string * jura_expr) -> jura_expr (**r Create a new concept/object *)
    | JFunCall : string -> list jura_expr -> jura_expr (**r function call *)
    | JSwitch : jura_expr -> list (switch_case * jura_expr) -> jura_expr -> jura_expr
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
    (* XXX Nothing yet -- denotational semantics should go here *)
  End Semantics.

  Section Evaluation.
    (* XXX Nothing yet -- evaluation semantics should go here *)
  End Evaluation.
End Jura.

