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

(* This is the [WIP] REFERENCE IMPLEMENTATION of the dynamic semantics of the
 * ERGO language.
 *
 * It is also being developed, and changing rapidly.
 *
 * -- Kartik, June 2018
 *)

Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EUtil.
Require Import ErgoSpec.Common.Utils.EResult.

Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCInline.

Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoC.

  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.

  Fixpoint ergo_inline_globals
           (ctxt : eval_context)
           (expr : ergoc_expr) : eresult ergoc_expr :=
    match expr with
    | EThisContract _ => esuccess expr
    | EThisClause _ => esuccess expr
    | EThisState _ => esuccess expr
    | EVar loc name =>
      match lookup String.string_dec (ctxt.(eval_context_local_env)) name with
      | Some _ => esuccess expr
      | None =>
        match lookup String.string_dec (ctxt.(eval_context_global_env)) name with
        | Some val => esuccess (EConst loc val)
        | None => esuccess expr
        end
      end
    | EConst _ _ => esuccess expr
    | EArray loc a =>
      elift (EArray loc)
            (fold_left
               (fun ls na =>
                  elift2 postpend ls (ergo_inline_globals ctxt na))
               a (esuccess nil))
    | EUnaryOp loc o e => elift (EUnaryOp loc o) (ergo_inline_globals ctxt e)
    | EBinaryOp loc o e1 e2 =>
      elift2 (EBinaryOp loc o) (ergo_inline_globals ctxt e1) (ergo_inline_globals ctxt e2)
    | EIf loc c t f =>
      elift3 (EIf loc)
             (ergo_inline_globals ctxt c)
             (ergo_inline_globals ctxt t)
             (ergo_inline_globals ctxt f)
    | ELet loc n t v b =>
      elift2 (fun v' b' => (ELet loc) n t v' b')
             (ergo_inline_globals ctxt v)
             (ergo_inline_globals (eval_context_update_local_env ctxt n dunit) b)
    | ERecord loc rs =>
      elift (ERecord loc)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctxt (snd nr))))
               rs (esuccess nil))
    | ENew loc n rs =>
      elift (ENew loc n)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctxt (snd nr))))
               rs (esuccess nil))
    | ECallFun loc fn args =>
      elift (ECallFun loc fn)
            (fold_left
               (fun ls nv =>
                  elift2 postpend ls (ergo_inline_globals ctxt nv))
               args (esuccess nil))
    | EMatch _ _ _ _ => TODO
    | EForeach loc rs whr fn =>
      elift3 (EForeach loc)
             (fold_left
                (fun ls nr =>
                   elift2 postpend ls
                          (elift (fun x => (fst nr, x)) (ergo_inline_globals ctxt (snd nr))))
                rs (esuccess nil))
             (match whr with
              | Some whr' => (elift Some) (ergo_inline_globals ctxt whr')
              | None => esuccess None
              end)
             (ergo_inline_globals ctxt fn)
    end.

  Definition ergo_inline_function
             (ctxt : eval_context)
             (fn : ergoc_function) : eresult ergoc_function :=
    match fn.(functionc_body) with
    | None => TODO
    | Some expr =>
      match eolift (ergo_inline_expr ctxt) (ergo_inline_globals ctxt expr) with
      | Success _ _ new_body =>
        esuccess (mkFuncC fn.(functionc_annot)
                               fn.(functionc_sig)
                                    (Some new_body))
      | Failure _ _ f => efailure f
      end
    end.

  Fixpoint ergo_eval_expr (ctxt : eval_context) (expr : ergoc_expr) : eresult ergo_data :=
    match expr with
    | EThisContract loc => efailure (SystemError loc "No `this' in ergoc")
    | EThisClause   loc => efailure (SystemError loc "No `clause' in ergoc")
    | EThisState    loc => efailure (SystemError loc "No `state' in ergoc")
    | EVar loc name =>
      let opt := lookup String.string_dec (ctxt.(eval_context_local_env)++ctxt.(eval_context_global_env)) name in
      eresult_of_option opt (RuntimeError loc ("Variable not found: " ++ name)%string)
    | EConst loc d => esuccess d

    | EArray loc es =>
      fold_left
        (fun ls new =>
           match ls with
           | Success _ _ (dcoll ls') =>
             match ergo_eval_expr ctxt new with
             | Success _ _ new' => esuccess (dcoll (ls' ++ (new'::nil)))
             | Failure _ _ f => efailure f
             end
           | Success _ _ _ => efailure (RuntimeError loc "This should never happen.")
           | Failure _ _ f => efailure f
           end)
        es (esuccess (dcoll nil))

    | EUnaryOp loc o e  =>
      match ergo_eval_expr ctxt e with
      | Success _ _ e' =>
        (* TODO this takes a type hierarchy as a list of string * strings. *)
        match ergo_unary_eval nil o e' with
        | Some r => esuccess r
        | None => efailure (RuntimeError loc "Unary operation failed.")
        end
      | Failure _ _ f => efailure f
      end
        
    | EBinaryOp loc o e1 e2 =>
      match ergo_eval_expr ctxt e1 with
      | Success _ _ e1' =>
        match ergo_eval_expr ctxt e2 with
        | Success _ _ e2' =>
          (* TODO this takes a type hierarchy as a list of string * strings. *)
          match ergo_binary_eval nil o e1' e2' with
          | Some r => esuccess r
          | None => efailure (RuntimeError loc "Binary operation failed.")
          end
        | Failure _ _ f => efailure f
        end
      | Failure _ _ f => efailure f
      end

    | EIf loc c t f =>
      match ergo_eval_expr ctxt c with
      | Success _ _ (dbool true) => ergo_eval_expr ctxt t
      | Success _ _ (dbool false) => ergo_eval_expr ctxt f
      | Success _ _ _ => efailure (RuntimeError loc "'If' condition not boolean.")
      | Failure _ _ f => efailure f
      end

    | ELet loc n t v e =>
      match ergo_eval_expr ctxt v with
      | Success _ _ v' =>
        let ctxt' := eval_context_update_local_env ctxt n v' in
        ergo_eval_expr ctxt' e
      | Failure _ _ f => efailure f
      end

    | ERecord loc rs =>
      fold_left
        (fun ls nv =>
           let name := fst nv in
           let value := snd nv in
           match ls with
           | Success _ _ (drec ls') =>
             match ergo_eval_expr ctxt value with
             (* TODO OpRecConcat to normalize shadowing properly *)
             | Success _ _ value' => esuccess (drec (ls' ++ ((name, value')::nil)))
             | Failure _ _ f => efailure f
             end
           | Success _ _ _ => efailure (RuntimeError loc "This should never happen.")
           | Failure _ _ f => efailure f
           end)
        rs (esuccess (drec nil))

    (* RIP modularity *)
    | ENew loc nr rs =>
      match
        fold_left
          (fun ls nv =>
             let name := fst nv in
             let value := snd nv in
             match ls with
             | Success _ _ (drec ls') =>
               match ergo_eval_expr ctxt value with
               (* TODO OpRecConcat to normalize shadowing properly *)
               | Success _ _ value' => esuccess (drec (ls' ++ ((name, value')::nil)))
               | Failure _ _ f => efailure f
               end
             | Success _ _ _ => efailure (RuntimeError loc "This should never happen.")
             | Failure _ _ f => efailure f
             end)
          rs (esuccess (drec nil))
      with
      | Failure _ _ f => efailure f
      | Success _ _ r => esuccess (dbrand (nr::nil) r)
      end

    (* EXPECTS: no function calls in expression *)
    | ECallFun loc fn args => efailure (SystemError loc "You forgot to inline a call...")

    | EMatch loc e pes f => TODO

    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach loc ((name,arr)::nil) None fn =>
      match ergo_eval_expr ctxt arr with
      | Failure _ _ f => efailure f
      | Success _ _ (dcoll arr') =>
        (elift dcoll)
          (emaplift
             (fun elt => ergo_eval_expr (eval_context_update_local_env ctxt name elt) fn)
             arr')
      | Success _ _ _ => efailure (RuntimeError loc "Foreach needs to be called on an array")
      end
    | EForeach loc _ _ _ =>
      efailure (RuntimeError loc "Failed to inline foreach")
    end.

  Definition ergoc_eval_decl
             (dctxt : eval_context)
             (decl : ergoc_declaration)
    : eresult (eval_context * option ergo_data) :=
    match decl with
    | DCExpr loc expr =>
      elift (fun x => (dctxt, Some x))
            ((eolift (ergo_eval_expr dctxt)) (ergo_inline_expr dctxt expr))
    | DCConstant loc name expr =>
      let expr' := eolift (ergo_eval_expr dctxt) (ergo_inline_expr dctxt expr) in
      eolift (fun val => esuccess (eval_context_update_global_env dctxt name val, None)) expr'
    | DCFunc loc name func =>
      elift (fun fn' =>
               (eval_context_update_function_env dctxt name fn', None))
            (ergo_inline_function dctxt func)
    | DCContract loc name contr => TODO
    end.

End ErgoC.

(*
Section Tests.

  Definition cow : string := "disco".
  Definition easy := EConst (dnat 0).
  Definition summ := EUnaryOp (OpNatUnary NatLog2) (EConst (dnat 1024)).
  Definition lettuce := ELet "cow" None (EConst (dnat 1024)) (EVar "cow").
  Definition cabbage := ELet "cow" None (EConst (dnat 2048)) lettuce.
  Definition records := ERecord ((cow, EConst (dnat 512))::(cow, EConst (dnat 4096))::nil).

  (* Compute = Eval vm_compute in *)
  Compute (ergo_eval_expr ergo_empty_context easy).
  Compute (ergo_eval_expr ergo_empty_context summ).
  Compute (ergo_eval_expr ergo_empty_context cabbage).
  Compute (ergo_eval_expr ergo_empty_context records).

End Tests.

 *)
