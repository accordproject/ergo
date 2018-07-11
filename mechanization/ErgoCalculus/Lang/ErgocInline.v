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
Require Import Common.Utils.EProvenance.

Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Translation.CTOtoErgo.

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

  Fixpoint ergo_map_expr
           (ctx : ergo_context)
           (fn : ergo_context -> ergo_expr -> option (eresult ergo_expr))
           (expr : ergo_expr)
    : eresult ergo_expr :=
    let maybe_fn :=
        fun expr'  =>
          match elift (fn ctx) expr' with
          | Success _ _ (Some r) => r
          | Success _ _ None => expr'
          | Failure _ _ f => efailure f
          end
    in
    maybe_fn
      match expr with
      | EThisContract _ => esuccess expr
      | EThisClause _ => esuccess expr
      | EThisState _ => esuccess expr
      | EVar _ _ => esuccess expr
      | EConst _ _ => esuccess expr
      | EArray loc a =>
        elift (EArray loc)
              (fold_left
                 (fun ls na =>
                    elift2 postpend ls (ergo_map_expr ctx fn na))
                 a (esuccess nil))
      | EUnaryOp loc o e =>
        elift (EUnaryOp loc o) (ergo_map_expr ctx fn e)
      | EBinaryOp loc o e1 e2 =>
        elift2 (EBinaryOp loc o) (ergo_map_expr ctx fn e1) (ergo_map_expr ctx fn e2)
      | EIf loc c t f =>
        elift3 (EIf loc)
               (ergo_map_expr ctx fn c)
               (ergo_map_expr ctx fn t)
               (ergo_map_expr ctx fn f)
      | ELet loc n t v b =>
        elift2 (fun v' b' => (ELet loc) n t v' b')
               (ergo_map_expr ctx fn v)
               (ergo_map_expr (ergo_ctx_update_local_env ctx n dunit) fn b)
      | ERecord loc rs =>
        elift (ERecord loc)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx fn (snd nr))))
                 rs (esuccess nil))
      | ENew loc n rs =>
        elift (ENew loc n)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx fn (snd nr))))
                 rs (esuccess nil))
      | ECallFun loc fn' args =>
        elift (ECallFun loc fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (ergo_map_expr ctx fn nv))
                         args (esuccess nil))
      | EForeach loc rs whr fn' =>
        elift3
          (EForeach loc)
          (fold_left
             (fun ls nr =>
                elift2 postpend ls
                       (elift (fun x => (fst nr, x)) (ergo_map_expr ctx fn (snd nr))))
             rs (esuccess nil))
          (match whr with
           | Some whr' => (elift Some) (ergo_map_expr ctx fn whr')
           | None => esuccess None
           end)
          (ergo_map_expr ctx fn fn')
      | EMatch _ _ _ _ => TODO
      end.

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

  Definition ergo_inline_foreach ctx := ergo_map_expr ctx ergo_inline_foreach'.

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

  Definition ergo_inline_functions ctx := ergo_map_expr ctx ergo_inline_functions'.

  Definition ergo_inline_expr := ergo_inline_functions.

End ErgoInline.
