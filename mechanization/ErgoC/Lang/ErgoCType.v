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
Require Import ErgoSpec.Common.Pattern.EPattern.

Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypeContext.

Require Import ErgoSpec.Ergo.Lang.Ergo.


Section ErgoCType.

  (*
  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.
*)

  Context {br : brand_relation}.
  Import ErgoCTypes.

  (*
  Fixpoint ergo_type_expr (ctxt : type_context) (expr : ergoc_expr) : eresult ergoc_type :=
    match expr with
    | EThisContract prov => efailure (SystemError prov "No `this' in ergoc")
    | EThisClause   prov => efailure (SystemError prov "No `clause' in ergoc")
    | EThisState    prov => efailure (SystemError prov "No `state' in ergoc")
    | EVar prov name =>
      let opt := lookup String.string_dec (ctxt.(type_context_local_env)++ctxt.(type_context_global_env)) name in
      eresult_of_option opt (RuntimeError prov ("Variable not found: " ++ name)%string)
    | EConst prov d =>
      eresult_of_option (infer_data_type d) (TypeError prov "Baaad constant.")
    | EArray prov es =>
      fold_left
        (fun ls new =>
           match ls with
           | Success _ _ (ErgoCTypes.tcoll ls') =>
             match ergo_type_expr ctxt new with
             | Success _ _ new' => esuccess (tcoll (ls' ++ (new'::nil)))
             | Failure _ _ f => efailure f
             end
           | Success _ _ _ => efailure (RuntimeError prov "This should never happen.")
           | Failure _ _ f => efailure f
           end)
        es (esuccess (tcoll ttop))
    | EUnaryOp prov o e => TODO
    (*
      match ergo_type_expr ctxt e with
      | Success _ _ e' =>
        (* TODO this takes a type hierarchy as a list of string * strings. *)
        match ergo_unary_eval nil o e' with
        | Some r => esuccess r
        | None => efailure (RuntimeError prov "Unary operation failed.")
        end
      | Failure _ _ f => efailure f
      end
     *)
    | EBinaryOp prov o e1 e2 =>
      match ergo_type_expr ctxt e1 with
      | Success _ _ e1' =>
        match ergo_type_expr ctxt e2 with
        | Success _ _ e2' =>
          (* TODO this takes a type hierarchy as a list of string * strings. *)
          (*
          match ergo_binary_eval nil o e1' e2' with
          | Some r => esuccess r
          | None => efailure (RuntimeError prov "Binary operation failed.")
          end
           *)
          TODO
        | Failure _ _ f => efailure f
        end
      | Failure _ _ f => efailure f
      end
    | EIf prov c t f =>
      match ergo_type_expr ctxt c with
      | Success _ _ (dbool true) => ergo_type_expr ctxt t
      | Success _ _ (dbool false) => ergo_type_expr ctxt f
      | Success _ _ _ => efailure (RuntimeError prov "'If' condition not boolean.")
      | Failure _ _ f => efailure f
      end
    | ELet prov n t v e =>
      match ergo_type_expr ctxt v with
      | Success _ _ v' =>
        let ctxt' := type_context_update_local_env ctxt n v' in
        ergo_type_expr ctxt' e
      | Failure _ _ f => efailure f
      end
    | ERecord prov rs =>
      fold_left
        (fun ls nv =>
           let name := fst nv in
           let value := snd nv in
           match ls with
           | Success _ _ (drec ls') =>
             match ergo_type_expr ctxt value with
             (* TODO OpRecConcat to normalize shadowing properly *)
             | Success _ _ value' => esuccess (drec (ls' ++ ((name, value')::nil)))
             | Failure _ _ f => efailure f
             end
           | Success _ _ _ => efailure (RuntimeError prov "This should never happen.")
           | Failure _ _ f => efailure f
           end)
        rs (esuccess (drec nil))
    (* RIP modularity *)
    | ENew prov nr rs =>
      match
        fold_left
          (fun ls nv =>
             let name := fst nv in
             let value := snd nv in
             match ls with
             | Success _ _ (drec ls') =>
               match ergo_type_expr ctxt value with
               (* TODO OpRecConcat to normalize shadowing properly *)
               | Success _ _ value' => esuccess (drec (ls' ++ ((name, value')::nil)))
               | Failure _ _ f => efailure f
               end
             | Success _ _ _ => efailure (RuntimeError prov "This should never happen.")
             | Failure _ _ f => efailure f
             end)
          rs (esuccess (drec nil))
      with
      | Failure _ _ f => efailure f
      | Success _ _ r => esuccess (dbrand (nr::nil) r)
      end
    (* EXPECTS: no function calls in expression *)
    | ECallFun prov fname args => function_not_inlined_error prov fname
    | ECallFunInGroup prov gname fname args => function_in_group_not_inlined_error prov gname fname
    | EMatch prov term pes default =>
      let lift_dbrand :=
          fun dat brand fn default =>
            match dat with
            | dbrand (br::nil) rcd =>
              if String.string_dec brand br then
                fn dat
              else
                default
            | _ => default
            end
      in
      match ergo_type_expr ctxt term with
      | Failure _ _ f => efailure f
      | Success _ _ dat =>
        fold_left
          (fun default_result pe =>
             match pe with
             | (CaseData prov d, res) =>
               if Data.data_eq_dec d dat then
                 ergo_type_expr ctxt res
               else
                 default_result
             | (CaseWildcard prov None, res) =>
               ergo_type_expr ctxt res
             | (CaseLet prov name None, res) =>
               ergo_type_expr (type_context_update_local_env ctxt name dat) res
             | (CaseLetOption prov name None, res) =>
               match dat with
               | dright dunit => default_result
               | dleft dat' => ergo_type_expr (type_context_update_local_env ctxt name dat') res
               | _ =>
                 efailure (RuntimeError prov "Matched LetOption without an option.")
               end
             | (CaseWildcard prov (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergo_type_expr ctxt res)
                           default_result
             | (CaseLet prov name (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergo_type_expr
                                          (type_context_update_local_env ctxt name dat')
                                          res)
                           default_result
             | (CaseLetOption prov name (Some typ), res) =>
               match dat with
               | dright dunit => default_result
               | dleft dat' =>
                 lift_dbrand dat' typ
                             (fun dat' => ergo_type_expr
                                            (type_context_update_local_env ctxt name dat')
                                            res)
                             default_result
               | _ =>
                 efailure (RuntimeError prov "Matched LetOption without an option.")
               end
             end)
          pes (ergo_type_expr ctxt default)
      end

    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach prov ((name,arr)::nil) None fn =>
      match ergo_type_expr ctxt arr with
      | Failure _ _ f => efailure f
      | Success _ _ (dcoll arr') =>
        (elift dcoll)
          (emaplift
             (fun elt => ergo_type_expr (type_context_update_local_env ctxt name elt) fn)
             arr')
      | Success _ _ _ => efailure (RuntimeError prov "Foreach needs to be called on an array")
      end
    | EForeach prov _ _ _ =>
      complex_foreach_in_calculus_error prov
    end.

  (*
  Definition ergoc_eval_decl
             (dctxt : eval_context)
             (decl : ergoc_declaration)
    : eresult (eval_context * option ergo_data) :=
    match decl with
    | DCExpr prov expr =>
      elift (fun x => (dctxt, Some x)) (ergo_eval_expr dctxt expr)
    | DCConstant prov name expr =>
      let expr' := ergo_eval_expr dctxt expr in
      eolift (fun val => esuccess (eval_context_update_global_env dctxt name val, None)) expr'
    | DCFunc prov name func =>
      esuccess (dctxt, None)
    | DCContract prov name contr =>
      esuccess (dctxt, None)
    end.
*)
*)

End ErgoCType.
