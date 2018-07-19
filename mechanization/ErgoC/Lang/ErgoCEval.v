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

Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoC.

  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.

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

    | EMatch loc e pes f => TODO "Match(eval)"

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
      elift (fun x => (dctxt, Some x)) (ergo_eval_expr dctxt expr)
    | DCConstant loc name expr =>
      let expr' := ergo_eval_expr dctxt expr in
      eolift (fun val => esuccess (eval_context_update_global_env dctxt name val, None)) expr'
    | DCFunc loc name func =>
      esuccess (eval_context_update_function_env dctxt name func, None)
    | DCContract loc name contr => TODO "Contract(decl)"
    end.

End ErgoC.
