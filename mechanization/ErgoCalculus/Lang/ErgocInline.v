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
Require Import Basics.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import Common.Utils.EUtil.
Require Import Common.Utils.EResult.
Require Import Common.Utils.ENames.
Require Import Common.Utils.EProvenance.

Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Translation.CTOtoErgo.

Require Import ErgoMap.

Require Ergo.
Require Import Ergo.
Require Import ErgoCalculus.
Definition ergo_expr := Ergo.laergo_expr.
Definition ergo_stmt := Ergo.laergo_stmt.
Definition ergo_function := Ergo.laergo_function.
Definition ergo_clause := Ergo.laergo_clause.
Definition ergo_contract := Ergo.laergo_contract.
Definition ergo_declaration := Ergo.laergo_declaration.
Definition ergo_module := Ergo.laergo_module.

Section ErgoInline.

  Definition ergo_map_expr_sane ctx fn expr :=
    @ergo_map_expr provenance absolute_name ergo_context ctx
                       (fun ctx name expr => ergo_ctx_update_local_env ctx name dunit)
                       fn expr.

  Definition ergo_inline_foreach' (ctx : ergo_context) (expr : ergo_expr) :=
    match expr with
    | EForeach loc rs whr fn =>
      (compose Some esuccess)
        (fold_right
           (fun rcd ker => (EUnaryOp loc OpFlatten) (EForeach loc (rcd::nil) whr ker))
           (match whr with
            | Some whr' => (EIf loc whr' (EArray loc (fn::nil)) (EArray loc nil))
            | None => (EArray loc (fn::nil))
            end)
           rs)
    | _ => None
    end.

  Definition ergo_inline_foreach ctx := ergo_map_expr_sane ctx ergo_inline_foreach'.

  Fixpoint ergo_letify_function'
           (prov : provenance)
           (body : ergo_expr)
           (args : list (string * ergo_expr)) : ergo_expr :=
    match args with
    | nil => body
    | (n,v)::rest => ELet prov n None v (ergo_letify_function' prov body rest)
    end.

  Definition ergo_letify_function (fn : ergoc_function) (args : list ergo_expr) :=
    match fn.(functionc_body) with
    | None => TODO
    | Some body =>
      match zip (map fst (fn.(functionc_sig).(sigc_params))) args with
      | Some args' => esuccess (ergo_letify_function' fn.(functionc_annot) body args')
      | None =>
        efailure (CompilationError
                    fn.(functionc_annot)
                    ("Wrong number of arguments for function.")%string)
      end
    end.

  Definition ergo_inline_functions' (ctx : ergo_context) (expr : ergo_expr) :=
  match expr with
  | ECallFun loc fn args => Some
      match lookup String.string_dec ctx.(ctx_function_env) fn with
      | Some fn' => ergo_letify_function fn' args
      | None => efailure (CompilationError loc ("Function " ++ fn ++ " not found.")%string)
      end
  | _ => None
  end.

  Definition ergo_inline_functions ctx := ergo_map_expr_sane ctx ergo_inline_functions'.

  Definition ergo_inline_expr := ergo_inline_functions.

End ErgoInline.
