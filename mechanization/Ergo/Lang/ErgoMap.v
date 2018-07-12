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

Require Import Ergo.

Section ErgoMap.

  Fixpoint ergo_map_expr {A : Set} {L : Set} {N : Set}
           (ctx : A)
           (ctx_add : A -> string -> @ergo_expr L N -> A)
           (fn : A -> @ergo_expr L N -> option (eresult (@ergo_expr L N)))
           (expr : @ergo_expr L N)
    : eresult (@ergo_expr L N) :=
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
                    elift2 postpend ls (ergo_map_expr ctx ctx_add fn na))
                 a (esuccess nil))
      | EUnaryOp loc o e =>
        elift (EUnaryOp loc o) (ergo_map_expr ctx ctx_add fn e)
      | EBinaryOp loc o e1 e2 =>
        elift2 (EBinaryOp loc o) (ergo_map_expr ctx ctx_add fn e1) (ergo_map_expr ctx ctx_add fn e2)
      | EIf loc c t f =>
        elift3 (EIf loc)
               (ergo_map_expr ctx ctx_add fn c)
               (ergo_map_expr ctx ctx_add fn t)
               (ergo_map_expr ctx ctx_add fn f)
      | ELet loc n t v b =>
        elift2 (fun v' b' => (ELet loc) n t v' b')
               (ergo_map_expr ctx ctx_add fn v)
               (ergo_map_expr (ctx_add ctx n v) ctx_add fn b)
      | ERecord loc rs =>
        elift (ERecord loc)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctx_add fn (snd nr))))
                 rs (esuccess nil))
      | ENew loc n rs =>
        elift (ENew loc n)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctx_add fn (snd nr))))
                 rs (esuccess nil))
      | ECallFun loc fn' args =>
        elift (ECallFun loc fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (ergo_map_expr ctx ctx_add fn nv))
                         args (esuccess nil))
      | EForeach loc rs whr fn' =>
        elift3
          (EForeach loc)
          (fold_left
             (fun ls nr =>
                elift2 postpend ls
                       (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctx_add fn (snd nr))))
             rs (esuccess nil))
          (match whr with
           | Some whr' => (elift Some) (ergo_map_expr ctx ctx_add fn whr')
           | None => esuccess None
           end)
          (ergo_map_expr ctx ctx_add fn fn')
      | EMatch _ _ _ _ => TODO
      end.

End ErgoMap.
