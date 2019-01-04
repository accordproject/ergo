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
Require Import ErgoSpec.Common.Utils.Misc.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Ast.

Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.

Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoCTEval.
  Context {m:brand_model}.

  Definition ergo_unary_builtin_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_builtin_eval := ErgoOps.Binary.eval.

  Fixpoint ergoct_eval_expr (ctxt : eval_context) (expr : ergoct_expr) : eresult ergo_data :=
    match expr with
    | EThisContract (prov,_) => contract_in_calculus_error prov
    | EThisClause   (prov,_) => clause_in_calculus_error prov
    | EThisState    (prov,_) => state_in_calculus_error prov
    | EVar (prov,_) name =>
      match lookup String.string_dec (ctxt.(eval_context_local_env)++ctxt.(eval_context_global_env)) name with
      | None => variable_name_not_found_error prov name
      | Some d => esuccess d
      end
    | EConst (prov,_) d => esuccess d
    | ENone (prov,_) => esuccess dnone
    | ESome (prov,_) e => elift dsome (ergoct_eval_expr ctxt e)
    | EArray (prov,_) es =>
      let rcoll :=
          fold_left
            (fun ls new =>
               match ls with
               | Success _ _ ls' =>
                 match ergoct_eval_expr ctxt new with
                 | Success _ _ new' => esuccess (ls' ++ (new'::nil))
                 | Failure _ _ f => efailure f
                 end
               | Failure _ _ f => efailure f
               end)
            es (esuccess nil)
      in
      elift dcoll rcoll
    (*** XXX - DISPATCH HERE *)
    | EBinaryOperator (prov,_) o e1 e2 =>
      eval_binary_operator_error prov o
    (*** XXX - DISPATCH HERE *)
    | EUnaryBuiltin (prov,_) o e  =>
      match ergoct_eval_expr ctxt e with
      | Success _ _ e' =>
        (* TODO this takes a type hierarchy as a list of string * strings. *)
        match ergo_unary_builtin_eval nil o e' with
        | Some r => esuccess r
        | None => eval_unary_builtin_error prov o
        end
      | Failure _ _ f => efailure f
      end
    | EBinaryBuiltin (prov,_) o e1 e2 =>
      match ergoct_eval_expr ctxt e1 with
      | Success _ _ e1' =>
        match ergoct_eval_expr ctxt e2 with
        | Success _ _ e2' =>
          (* TODO this takes a type hierarchy as a list of string * strings. *)
          match ergo_binary_builtin_eval nil o e1' e2' with
          | Some r => esuccess r
          | None => eval_binary_builtin_error prov o
          end
        | Failure _ _ f => efailure f
        end
      | Failure _ _ f => efailure f
      end
    | EIf (prov,_) c t f =>
      match ergoct_eval_expr ctxt c with
      | Success _ _ (dbool true) => ergoct_eval_expr ctxt t
      | Success _ _ (dbool false) => ergoct_eval_expr ctxt f
      | Success _ _ _ => eval_if_not_boolean_error prov
      | Failure _ _ f => efailure f
      end
    | ELet (prov,_) n t v e =>
      match ergoct_eval_expr ctxt v with
      | Success _ _ v' =>
        let ctxt' := eval_context_update_local_env ctxt n v' in
        ergoct_eval_expr ctxt' e
      | Failure _ _ f => efailure f
      end
    | ERecord prov rs =>
      let rrec :=
          fold_left
            (fun ls nv =>
               let name := fst nv in
               let value := snd nv in
               match ls with
               | Success _ _ ls' =>
                 match ergoct_eval_expr ctxt value with
                 (* TODO OpRecConcat to normalize shadowing properly *)
                 | Success _ _ value' => esuccess (ls' ++ ((name, value')::nil))
                 | Failure _ _ f => efailure f
                 end
               | Failure _ _ f => efailure f
               end)
            rs (esuccess nil)
      in
      elift drec rrec
    (* RIP modularity *)
    | ENew (prov,_) nr rs =>
      match
        fold_left
          (fun ls nv =>
             let name := fst nv in
             let value := snd nv in
             match ls with
             | Success _ _ ls' =>
               match ergoct_eval_expr ctxt value with
               (* TODO OpRecConcat to normalize shadowing properly *)
               | Success _ _ value' => esuccess (ls' ++ ((name, value')::nil))
               | Failure _ _ f => efailure f
               end
             | Failure _ _ f => efailure f
             end)
          rs (esuccess nil)
      with
      | Failure _ _ f => efailure f
      | Success _ _ r => esuccess (dbrand (nr::nil) (drec r))
      end
    (* EXPECTS: no function calls in expression *)
    | ECallFun (prov,_) fname args => function_not_inlined_error prov "eval" fname
    | ECallFunInGroup (prov,_) gname fname args => function_in_group_not_inlined_error prov gname fname
    | EMatch (prov,_) term pes default =>
      let lift_dbrand :=
          fun dat brand fn default => 
            match dat with
            | dbrand (br::nil) rcd =>
              if sub_brands_dec brand_relation_brands (br::nil) (brand::nil) then
                fn dat
              else
                default
            | _ => default
            end
      in
      match ergoct_eval_expr ctxt term with
      | Failure _ _ f => efailure f
      | Success _ _ dat =>
        fold_left
          (fun default_result pe =>
             match pe with
             | (CaseData prov d, res) =>
               if Data.data_eq_dec d dat then
                 ergoct_eval_expr ctxt res
               else
                 default_result
             | (CaseWildcard prov None, res) =>
               ergoct_eval_expr ctxt res
             | (CaseLet prov name None, res) =>
               ergoct_eval_expr (eval_context_update_local_env ctxt name dat) res
             | (CaseLetOption prov name None, res) =>
               match dat with
               | dleft dat' => ergoct_eval_expr (eval_context_update_local_env ctxt name dat') res
               | _ => default_result
               end
             | (CaseWildcard prov (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergoct_eval_expr ctxt res)
                           default_result
             | (CaseLet prov name (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergoct_eval_expr
                                          (eval_context_update_local_env ctxt name dat')
                                          res)
                           default_result
             | (CaseLetOption prov name (Some typ), res) =>
               match dat with
               | dleft dat' =>
                lift_dbrand dat' typ
                            (fun dat' => ergoct_eval_expr
                                            (eval_context_update_local_env ctxt name dat')
                                            res)
                            default_result
               | _ => default_result
               end
             end)
          pes (ergoct_eval_expr ctxt default)
       end

    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach (prov,_) ((name,arr)::nil) None fn =>
      match ergoct_eval_expr ctxt arr with
      | Failure _ _ f => efailure f
      | Success _ _ (dcoll arr') =>
        (elift dcoll)
          (emaplift
             (fun elt => ergoct_eval_expr (eval_context_update_local_env ctxt name elt) fn)
             arr')
      | Success _ _ _ => eval_foreach_not_on_array_error prov
      end
    | EForeach (prov,_) _ _ _ =>
      complex_foreach_in_calculus_error prov
    end.

  Definition ergoct_eval_decl
             (dctxt : eval_context)
             (decl : ergoct_declaration)
    : eresult (eval_context * option ergo_data) :=
    match decl with
    | DCTExpr (prov,_) expr =>
      elift (fun x => (dctxt, Some x)) (ergoct_eval_expr dctxt expr)
    | DCTConstant (prov,_) name ta expr =>
      let expr' := ergoct_eval_expr dctxt expr in
      eolift (fun val => esuccess (eval_context_update_global_env dctxt name val, None)) expr'
    | DCTFunc prov name func =>
      esuccess (dctxt, None)
    | DCTContract prov name contr =>
      esuccess (dctxt, None)
    end.

End ErgoCTEval.
