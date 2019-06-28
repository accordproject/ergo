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

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoMap.
  Context {A:Set}. (* For expression annotations *)
  Context {A':Set}. (* For type annotations *)
  Context {N:Set}. (* For names *)

  Fixpoint ergo_map_expr {C : Set}
           (ctx : C)
           (ctxt_new_variable_scope : C -> string -> @ergo_expr A A' N -> C)
           (fn : C -> @ergo_expr A A' N -> option (eresult (@ergo_expr A A' N)))
           (expr : @ergo_expr A A' N)
    : eresult (@ergo_expr A A' N) :=
    let maybe_fn := elift_maybe (fn ctx) in
    maybe_fn
      match expr with
      | EThisContract _ => esuccess expr nil
      | EThisClause _ => esuccess expr nil
      | EThisState _ => esuccess expr nil
      | EVar _ _ => esuccess expr nil
      | EConst _ _ => esuccess expr nil
      | ENone _ => esuccess expr nil
      | ESome loc e =>
        elift (ESome loc) (ergo_map_expr ctx ctxt_new_variable_scope fn e)
      | EArray loc a =>
        elift (EArray loc)
              (fold_left
                 (fun ls na =>
                    elift2 postpend ls (ergo_map_expr ctx ctxt_new_variable_scope fn na))
                 a (esuccess nil nil))
      | EUnaryOperator loc o e =>
        elift (EUnaryOperator loc o)
              (ergo_map_expr ctx ctxt_new_variable_scope fn e)
      | EBinaryOperator loc o e1 e2 =>
        elift2 (EBinaryOperator loc o)
               (ergo_map_expr ctx ctxt_new_variable_scope fn e1)
               (ergo_map_expr ctx ctxt_new_variable_scope fn e2)
      | EUnaryBuiltin loc o e =>
        elift (EUnaryBuiltin loc o) (ergo_map_expr ctx ctxt_new_variable_scope fn e)
      | EBinaryBuiltin loc o e1 e2 =>
        elift2 (EBinaryBuiltin loc o)
               (ergo_map_expr ctx ctxt_new_variable_scope fn e1)
               (ergo_map_expr ctx ctxt_new_variable_scope fn e2)
      | EIf loc c t f =>
        elift3 (EIf loc)
               (ergo_map_expr ctx ctxt_new_variable_scope fn c)
               (ergo_map_expr ctx ctxt_new_variable_scope fn t)
               (ergo_map_expr ctx ctxt_new_variable_scope fn f)
      | ELet loc n t v b =>
        elift2 (fun v' b' => (ELet loc) n t v' b')
               (ergo_map_expr ctx ctxt_new_variable_scope fn v)
               (ergo_map_expr (ctxt_new_variable_scope ctx n v) ctxt_new_variable_scope fn b)
      | EPrint loc v b =>
        elift2 (fun v' b' => (EPrint loc) v' b')
               (ergo_map_expr ctx ctxt_new_variable_scope fn v)
               (ergo_map_expr ctx ctxt_new_variable_scope fn b)
      | ERecord loc rs =>
        elift (ERecord loc)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctxt_new_variable_scope fn (snd nr))))
                 rs (esuccess nil nil))
      | ENew loc n rs =>
        elift (ENew loc n)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctxt_new_variable_scope fn (snd nr))))
                 rs (esuccess nil nil))
      | ECallFun loc fn' args =>
        elift (ECallFun loc fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (ergo_map_expr ctx ctxt_new_variable_scope fn nv))
                         args (esuccess nil nil))
      | ECallFunInGroup loc gn fn' args =>
        elift (ECallFunInGroup loc gn fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (ergo_map_expr ctx ctxt_new_variable_scope fn nv))
                         args (esuccess nil nil))
      | EForeach loc rs whr fn' =>
        elift3
          (EForeach loc)
          (fold_left
             (fun ls nr =>
                elift2 postpend ls
                       (elift (fun x => (fst nr, x)) (ergo_map_expr ctx ctxt_new_variable_scope fn (snd nr))))
             rs (esuccess nil nil))
          (match whr with
           | Some whr' => (elift Some) (ergo_map_expr ctx ctxt_new_variable_scope fn whr')
           | None => esuccess None nil
           end)
          (ergo_map_expr ctx ctxt_new_variable_scope fn fn')

      | EMatch loc expr pes def =>
        eolift
          (fun expr' =>
             eolift
               (fun def' =>
                  elift (fun pes' => EMatch loc expr' pes' def')
                        (fold_right
                           (fun pe prev =>
                              elift2
                                (fun pe' prev' => pe' :: prev')
                                match pe with
                                | (CaseData _ _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr ctx ctxt_new_variable_scope fn e)
                                | (CaseWildcard _ _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr ctx ctxt_new_variable_scope fn e)
                                | (CaseLet _ name _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr (ctxt_new_variable_scope ctx name expr')
                                                       ctxt_new_variable_scope fn e)
                                | (CaseLetOption _ name _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr (ctxt_new_variable_scope ctx name expr')
                                                       ctxt_new_variable_scope fn e)
                                end
                                prev)
                           (esuccess nil nil)
                           pes))
               (ergo_map_expr ctx ctxt_new_variable_scope fn def))
          (ergo_map_expr ctx ctxt_new_variable_scope fn expr)
      end.

End ErgoMap.
