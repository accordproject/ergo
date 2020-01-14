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

Require Import List.
Require Import String.
Require Import ZArith.
Require Import EquivDec.
Require Import ToString.
Require Import Utils.
Require Import OptimizerLogger.

Section Test.
  Context {A:Type}.

  (* nraenv optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nraenv_token_type : Set.
  Axiom OPTIMIZER_LOGGER_nraenv_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_nraenv_token_type.
  Axiom OPTIMIZER_LOGGER_nraenv_step :
    OPTIMIZER_LOGGER_nraenv_token_type -> String.string -> A -> A -> OPTIMIZER_LOGGER_nraenv_token_type.
  Axiom OPTIMIZER_LOGGER_nraenv_endPass :
    OPTIMIZER_LOGGER_nraenv_token_type -> A -> OPTIMIZER_LOGGER_nraenv_token_type.

  (* nnrc optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nnrc_token_type : Set.
  Axiom OPTIMIZER_LOGGER_nnrc_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_nnrc_token_type.
  Axiom OPTIMIZER_LOGGER_nnrc_step :
    OPTIMIZER_LOGGER_nnrc_token_type -> String.string -> A -> A -> OPTIMIZER_LOGGER_nnrc_token_type.
  Axiom OPTIMIZER_LOGGER_nnrc_endPass :
    OPTIMIZER_LOGGER_nnrc_token_type -> A -> OPTIMIZER_LOGGER_nnrc_token_type.

  (* nnrs_imp optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_token_type : Set.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_step :
    OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> String.string ->
    A -> A -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_expr_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_expr_token_type -> A -> OPTIMIZER_LOGGER_nnrs_imp_expr_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type : Set.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_step :
    OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> String.string ->
    A -> A -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.

  Axiom OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type -> A -> OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_token_type : Set.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

  Axiom OPTIMIZER_LOGGER_nnrs_imp_step :
    OPTIMIZER_LOGGER_nnrs_imp_token_type -> String.string ->
    A -> A -> OPTIMIZER_LOGGER_nnrs_imp_token_type.
  Axiom OPTIMIZER_LOGGER_nnrs_imp_endPass :
    OPTIMIZER_LOGGER_nnrs_imp_token_type -> A -> OPTIMIZER_LOGGER_nnrs_imp_token_type.

  (* dnnrc optimizer logger support *)
  Axiom OPTIMIZER_LOGGER_dnnrc_token_type : Set.

  Axiom OPTIMIZER_LOGGER_dnnrc_startPass :
    String.string -> A -> OPTIMIZER_LOGGER_dnnrc_token_type.

  Axiom OPTIMIZER_LOGGER_dnnrc_step :
    OPTIMIZER_LOGGER_dnnrc_token_type -> String.string ->
    A -> A ->
    OPTIMIZER_LOGGER_dnnrc_token_type.
  Axiom OPTIMIZER_LOGGER_dnnrc_endPass :
    OPTIMIZER_LOGGER_dnnrc_token_type -> A -> OPTIMIZER_LOGGER_dnnrc_token_type.

End Test.

Extract Constant OPTIMIZER_LOGGER_nraenv_token_type => "Util.nraenv_logger_token_type".
Extract Constant OPTIMIZER_LOGGER_nraenv_startPass =>
"(fun name input -> Logger.nraenv_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_step =>
"(fun token name input output -> Logger.nraenv_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_nraenv_endPass =>
"(fun token output -> Logger.nraenv_log_endPass token output)".

Extract Constant OPTIMIZER_LOGGER_nnrc_token_type => "Util.nnrc_logger_token_type".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_startPass =>
"(fun name input -> Logger.nnrc_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_step =>
"(fun token name input output -> Logger.nnrc_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrc_endPass =>
"(fun token output -> Logger.nnrc_log_endPass token output)".

Extract Constant OPTIMIZER_LOGGER_nnrs_imp_expr_token_type => "Util.nnrs_imp_expr_logger_token_type".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_startPass =>
"(fun name input -> Logger.nnrs_imp_expr_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_step =>
"(fun token name input output -> Logger.nnrs_imp_expr_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_expr_endPass =>
"(fun token output -> Logger.nnrs_imp_expr_log_endPass token output)".

Extract Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_token_type => "Util.nnrs_imp_stmt_logger_token_type".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_startPass =>
"(fun name input -> Logger.nnrs_imp_stmt_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_step =>
"(fun token name input output -> Logger.nnrs_imp_stmt_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_stmt_endPass =>
"(fun token output -> Logger.nnrs_imp_stmt_log_endPass token output)".

Extract Constant OPTIMIZER_LOGGER_nnrs_imp_token_type => "Util.nnrs_imp_logger_token_type".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_startPass =>
"(fun name input -> Logger.nnrs_imp_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_step =>
"(fun token name input output -> Logger.nnrs_imp_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_nnrs_imp_endPass =>
"(fun token output -> Logger.nnrs_imp_log_endPass token output)".

Extract Constant OPTIMIZER_LOGGER_dnnrc_token_type => "Util.dnnrc_logger_token_type".
Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_startPass =>
"(fun name input -> Logger.dnnrc_log_startPass (Util.string_of_char_list name) input)".
Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_step =>
"(fun token name input output -> Logger.dnnrc_log_step token (Util.string_of_char_list name) input output)".
Extract Inlined Constant OPTIMIZER_LOGGER_dnnrc_endPass =>
"(fun token output -> Logger.dnnrc_log_endPass token output)".

