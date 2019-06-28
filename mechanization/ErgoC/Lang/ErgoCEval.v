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

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.

Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoCTEval.
  Context {m:brand_model}.

  Definition ergo_unary_builtin_eval
             (prov:provenance) (o:unary_op) (d:ergo_data) : eresult ergo_data :=
    match ErgoOps.Unary.eval brand_relation_brands o d with
    | Some r => esuccess r nil
    | None => eval_unary_builtin_error prov o
    end.
  Definition ergo_binary_builtin_eval
             (prov:provenance) (o:binary_op) (d1 d2:ergo_data) : eresult ergo_data :=
    match ErgoOps.Binary.eval brand_relation_brands o d1 d2 with
    | Some r => esuccess r nil
    | None => eval_binary_builtin_error prov o
    end.

  Fixpoint ergoct_eval_expr (ctxt : eval_context) (expr : ergoct_expr) : eresult ergo_data :=
    match expr with
    | EThisContract (prov,_) => contract_in_calculus_error prov
    | EThisClause   (prov,_) => clause_in_calculus_error prov
    | EThisState    (prov,_) => state_in_calculus_error prov
    | EVar (prov,_) name =>
      match lookup String.string_dec (ctxt.(eval_context_local_env)++ctxt.(eval_context_global_env)) name with
      | None => variable_name_not_found_error prov name
      | Some d => esuccess d nil
      end
    | EConst (prov,_) d => esuccess d nil
    | ENone (prov,_) => esuccess dnone nil
    | ESome (prov,_) e => elift dsome (ergoct_eval_expr ctxt e)
    | EArray (prov,_) es =>
      let rcoll := emaplift (ergoct_eval_expr ctxt) es in
      elift dcoll rcoll
    | EUnaryOperator (prov,_) o e =>
      eval_unary_operator_error prov o
    | EBinaryOperator (prov,_) o e1 e2 =>
      eval_binary_operator_error prov o
    | EUnaryBuiltin (prov,_) o e  =>
      eolift
        (ergo_unary_builtin_eval prov o)
        (ergoct_eval_expr ctxt e)
    | EBinaryBuiltin (prov,_) o e1 e2 =>
      eolift2
        (ergo_binary_builtin_eval prov o)
        (ergoct_eval_expr ctxt e1)
        (ergoct_eval_expr ctxt e2)
    | EIf (prov,_) c t f =>
      eolift
        (fun d =>
           match d with
           | dbool true => ergoct_eval_expr ctxt t
           | dbool false => ergoct_eval_expr ctxt f
           | _ => eval_if_not_boolean_error prov
           end)
        (ergoct_eval_expr ctxt c)
    | ELet (prov,_) n t e1 e2 =>
      eolift
        (fun d =>
           let ctxt' := eval_context_update_local_env ctxt n d in
           ergoct_eval_expr ctxt' e2)
        (ergoct_eval_expr ctxt e1)
    | EPrint (prov,_) v e =>
      print_in_calculus_error prov
    | ERecord prov rs =>
      let rrec :=
          emaplift
            (fun nv =>
               let att := fst nv in
               let e := snd nv in
               elift (fun d => (att, d)) (ergoct_eval_expr ctxt e))
            rs
      in
      elift drec (elift rec_sort rrec)
    | ENew (prov,_) nr rs =>
      let rrec :=
          emaplift
            (fun nv =>
               let att := fst nv in
               let e := snd nv in
               elift (fun d => (att, d)) (ergoct_eval_expr ctxt e))
            rs
      in
      elift (fun r => (dbrand (nr::nil) (drec (rec_sort r)))) rrec
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
      let apply_match dat :=
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
      in
      eolift apply_match (ergoct_eval_expr ctxt term)
    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach (prov,_) ((name,arr)::nil) None fn =>
      let rcoll :=
          eolift
            (fun d =>
               match d with
               | dcoll arr' =>
                 emaplift
                   (fun elt => ergoct_eval_expr (eval_context_update_local_env ctxt name elt) fn)
                   arr'
               | _ => eval_foreach_not_on_array_error prov
               end) (ergoct_eval_expr ctxt arr)
      in
      elift dcoll rcoll
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
      eolift (fun val => esuccess (eval_context_update_global_env dctxt name val, None) nil) expr'
    | DCTFunc prov name func =>
      esuccess (dctxt, None) nil
    | DCTContract prov name contr =>
      esuccess (dctxt, None) nil
    end.

End ErgoCTEval.
