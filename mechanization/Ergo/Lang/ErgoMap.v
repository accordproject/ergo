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
           (ctxt_new_variable_scope : C -> string -> @ergo_expr A A' N -> C)      (* Apply when scope changes *)
           (fn : C -> @ergo_expr A A' N -> option (eresult (@ergo_expr A A' N)))  (* The mapped function *)
           (ctx : C)
           (expr : @ergo_expr A A' N)
    : eresult (@ergo_expr A A' N) :=
    let maybe_fn := elift_maybe (fn ctx) in
    let apply_map := ergo_map_expr ctxt_new_variable_scope fn in
    maybe_fn
      match expr with
      | EThis _ => esuccess expr nil
      | EThisContract _ => esuccess expr nil
      | EThisClause _ => esuccess expr nil
      | EThisState _ => esuccess expr nil
      | EVar _ _ => esuccess expr nil
      | EConst _ _ => esuccess expr nil
      | ENone _ => esuccess expr nil
      | EText loc a =>
        elift (EText loc)
              (fold_left
                 (fun ls na =>
                    elift2 postpend ls (apply_map ctx na))
                 a (esuccess nil nil))
      | ESome loc e =>
        elift (ESome loc) (apply_map ctx e)
      | EArray loc a =>
        elift (EArray loc)
              (fold_left
                 (fun ls na =>
                    elift2 postpend ls (apply_map ctx na))
                 a (esuccess nil nil))
      | EUnaryOperator loc o e =>
        elift (EUnaryOperator loc o)
              (apply_map ctx e)
      | EBinaryOperator loc o e1 e2 =>
        elift2 (EBinaryOperator loc o)
               (apply_map ctx e1)
               (apply_map ctx e2)
      | EUnaryBuiltin loc o e =>
        elift (EUnaryBuiltin loc o) (apply_map ctx e)
      | EBinaryBuiltin loc o e1 e2 =>
        elift2 (EBinaryBuiltin loc o)
               (apply_map ctx e1)
               (apply_map ctx e2)
      | EIf loc c t f =>
        elift3 (EIf loc)
               (apply_map ctx c)
               (apply_map ctx t)
               (apply_map ctx f)
      | ELet loc n t v b =>
        elift2 (fun v' b' => (ELet loc) n t v' b')
               (apply_map ctx v)
               (apply_map (ctxt_new_variable_scope ctx n v) b)
      | EPrint loc v b =>
        elift2 (fun v' b' => (EPrint loc) v' b')
               (apply_map ctx v)
               (apply_map ctx b)
      | ERecord loc rs =>
        elift (ERecord loc)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (apply_map ctx (snd nr))))
                 rs (esuccess nil nil))
      | ENew loc n rs =>
        elift (ENew loc n)
              (fold_left
                 (fun ls nr =>
                    elift2 postpend ls
                           (elift (fun x => (fst nr, x)) (apply_map ctx (snd nr))))
                 rs (esuccess nil nil))
      | ECallFun loc fn' args =>
        elift (ECallFun loc fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (apply_map ctx nv))
                         args (esuccess nil nil))
      | ECallFunInGroup loc gn fn' args =>
        elift (ECallFunInGroup loc gn fn')
              (fold_left (fun ls nv =>
                            elift2 postpend ls (apply_map ctx nv))
                         args (esuccess nil nil))
      | EForeach loc rs whr r =>
        let rs_ctx' :=
            let proc_one ctx (nr:string * @ergo_expr A A' N) :=
                let (n,e) := nr in
                elift (fun x => (x,(ctxt_new_variable_scope ctx n e)))
                      (elift (fun x => (n, x)) (apply_map ctx e))
            in
            elift_context_fold_left
              proc_one rs ctx
        in
        eolift
          (fun xy : list (string * @ergo_expr A A' N) * C =>
             let (rs',ctx) := xy in
             let whr' :=
                 match whr with
                 | Some whr' => (elift Some) (apply_map ctx whr')
                 | None => esuccess None nil
                 end
             in
             let r' := apply_map ctx r in
             elift3 (EForeach loc) (esuccess rs' nil) whr' r')
          rs_ctx'
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
                                        (apply_map ctx e)
                                | (CaseWildcard _ _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (apply_map ctx e)
                                | (CaseLet _ name _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr
                                           ctxt_new_variable_scope fn (ctxt_new_variable_scope ctx name expr')
                                           e)
                                | (CaseLetOption _ name _, e) =>
                                  elift (fun x => (fst pe, x))
                                        (ergo_map_expr
                                           ctxt_new_variable_scope fn (ctxt_new_variable_scope ctx name expr')
                                           e)
                                end
                                prev)
                           (esuccess nil nil)
                           pes))
               (apply_map ctx def))
          (apply_map ctx expr)
      end.

End ErgoMap.
