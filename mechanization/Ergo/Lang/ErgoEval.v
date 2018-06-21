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

(* This is the [WIP] REFERENCE IMPLEMENTATION of the dynamic semantics of the ERGO
 * language.
 *   It is also being developed, and changing rapidly.
 *
 * -- Kartik, June 2018
 *)

Require Import Ergo.
Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import Common.Utils.EResult.

Definition ergo_data := ErgoData.data.

Section ErgoEval.

  Record ergo_context :=
    mkContext
      { function_list : list (string * ergo_function);
        clause_list : list ergo_clause;
        contract_list : list ergo_contract;
        environment_list : list (string * ergo_data);
        this_clause : ergo_data;
        this_contract : ergo_data;
        this_state : ergo_data;
        this_emit : ergo_data;
        }.

  Definition ergo_empty_context :=
    mkContext nil nil nil nil dunit dunit dunit dunit.

  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.

  Definition ergo_context_update_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(function_list)
              ctx.(clause_list)
              ctx.(contract_list)
              ((name, value)::ctx.(environment_list))
              ctx.(this_clause)
              ctx.(this_contract)
              ctx.(this_state)
              ctx.(this_emit).

  Definition ergo_context_update_env' (ctx : ergo_context) (items : list (string * ergo_data)) : ergo_context :=
    fold_left (fun ctx' item => ergo_context_update_env ctx' (fst item) (snd item)) items ctx.

Fixpoint ergo_eval_expr (ctx : ergo_context) (expr : ergo_expr) : eresult ergo_data :=
  match expr with
  | EThisContract => esuccess ctx.(this_contract)
  | EThisClause => esuccess ctx.(this_clause)
  | EThisState => esuccess ctx.(this_state)
  | EThisEmit => esuccess ctx.(this_emit)    (* can be removed *)
  | EVar name =>
    let opt := lookup String.string_dec ctx.(environment_list) name in
    eresult_of_option opt (RuntimeError ("Variable not found: " ++ name))
  | EConst d => esuccess d

  | EArray es =>
    fold_left
      (fun ls new =>
         match ls with
         | Success _ _ (dcoll ls') =>
           match ergo_eval_expr ctx new with
           | Success _ _ new' => esuccess (dcoll (ls' ++ (new'::nil)))
           | Failure _ _ f => efailure f
           end
         | Success _ _ _ => efailure (RuntimeError "This should never happen.")
         | Failure _ _ f => efailure f
         end)
      es (esuccess (dcoll nil))

  | EUnaryOp o e  =>
    match ergo_eval_expr ctx e with
    | Success _ _ e' =>
      (* TODO this takes a type hierarchy as a list of string * strings. *)
      match ergo_unary_eval nil o e' with
      | Some r => esuccess r
      | None => efailure (RuntimeError "Unary operation failed.")
      end
    | Failure _ _ f => efailure f
    end
    
  | EBinaryOp o e1 e2 =>
    match ergo_eval_expr ctx e1 with
    | Success _ _ e1' =>
      match ergo_eval_expr ctx e2 with
      | Success _ _ e2' =>
        (* TODO this takes a type hierarchy as a list of string * strings. *)
        match ergo_binary_eval nil o e1' e2' with
        | Some r => esuccess r
        | None => efailure (RuntimeError "Binary operation failed.")
        end
      | Failure _ _ f => efailure f
      end
    | Failure _ _ f => efailure f
    end

  | EIf c t f =>
    match ergo_eval_expr ctx c with
    | Success _ _ (dbool true) => ergo_eval_expr ctx t
    | Success _ _ (dbool false) => ergo_eval_expr ctx f
    | Success _ _ _ => efailure (RuntimeError "'If' condition not boolean.")
    | Failure _ _ f => efailure f
    end

  | ELet n t v e =>
    match ergo_eval_expr ctx v with
    | Success _ _ v' =>
      let ctx' := ergo_context_update_env ctx n v' in
      ergo_eval_expr ctx' e
    | Failure _ _ f => efailure f
    end

  | ERecord rs =>
    fold_left
      (fun ls nv =>
         let name := fst nv in
         let value := snd nv in
         match ls with
         | Success _ _ (drec ls') =>
           match ergo_eval_expr ctx value with
             (* TODO OpRecConcat to normalize shadowing properly *)
           | Success _ _ value' => esuccess (drec (ls' ++ ((name, value')::nil)))
           | Failure _ _ f => efailure f
           end
         | Success _ _ _ => efailure (RuntimeError "This should never happen.")
         | Failure _ _ f => efailure f
         end)
      rs (esuccess (drec nil))

  | ENew nr vs => esuccess dunit
  | ECallFun fn args =>
    match lookup String.string_dec ctx.(function_list) fn with
    | Some fn' =>
      let lam := fn'.(function_lambda) in
      let nms := lam.(lambda_params) in
      let bod := lam.(lambda_body) in
      esuccess dunit
    | None => efailure (RuntimeError ("Function " ++ fn ++ " not found."))
    end
  | EMatch e pes f => efailure (RuntimeError "Unimplemented TODO")
  | EForeach ls whr f => efailure (RuntimeError "Unimplemented TODO")
  | ELiftError e1 e2 => efailure (RuntimeError "Unimplemented TODO") (* ignore for now *)
  end.

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

End ErgoEval.