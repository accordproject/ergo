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

(** ErgoWasm is an IL for Wasm *)

(** * Abstract Syntax *)

Require Import String.
Require Import List.
Require Import Qcert.Driver.CompEval.
Require Import Qcert.EJson.Model.ForeignEJson.
Require Import Qcert.EJson.Model.EJson.
Require Import Qcert.WasmAst.Lang.WasmAst.
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Backend.Qcert.QcertEJson.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.

Section ErgoWasm.
  Context {m : brand_model}.

  (** WASM programs are in AST form *)
  (** Same type as in Q*cert *)
  Definition wasm_ast : Set := wasm_ast.
  Definition wasm_ast_eval :brand_relation_t -> wasm_ast -> jbindings -> option ejson
    := @wasm_ast_eval enhanced_ejson.
  Definition wasm_ast_to_string : wasm_ast -> nstring := wasm_ast_to_string.

End ErgoWasm.

Extract Constant wasm_ast => "Qcert_lib.Wasm_ast.t".
Extract Constant wasm_ast_eval => "Qcert_lib.Wasm_ast.eval".
Extract Constant wasm_ast_to_string => "Qcert_lib.Wasm_ast.to_string".
