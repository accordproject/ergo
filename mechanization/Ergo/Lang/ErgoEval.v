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
      { ctx_function_list : list (string * ergo_function);
        ctx_clause_list : list ergo_clause;
        ctx_contract_list : list ergo_contract;
        ctx_global_env : list (string * ergo_data);
        ctx_local_env : list (string * ergo_data);
        ctx_this_clause : ergo_data;
        ctx_this_contract : ergo_data;
        ctx_this_state : ergo_data;
        ctx_this_emit : ergo_data;
        }.

  Definition ergo_empty_context :=
    mkContext nil nil nil nil nil dunit dunit dunit dunit.

  Definition TODO {A : Set} : eresult A := efailure (SystemError "Feature not implemented.").

  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.

  Definition ergo_context_update_global_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_list)
              ctx.(ctx_clause_list)
              ctx.(ctx_contract_list)
              ((name, value)::ctx.(ctx_global_env))
              (ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_context_update_local_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_list)
              ctx.(ctx_clause_list)
              ctx.(ctx_contract_list)
              (ctx.(ctx_global_env))
              ((name, value)::ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_context_update_local_env' (ctx : ergo_context) (items : list (string * ergo_data)) : ergo_context :=
    fold_left (fun ctx' item => ergo_context_update_local_env ctx' (fst item) (snd item)) items ctx.

Fixpoint ergo_eval_expr (ctx : ergo_context) (expr : ergo_expr) : eresult ergo_data :=
  match expr with
  | EThisContract => esuccess ctx.(ctx_this_contract)
  | EThisClause => esuccess ctx.(ctx_this_clause)
  | EThisState => esuccess ctx.(ctx_this_state)
  | EVar name =>
    let opt := lookup String.string_dec (ctx.(ctx_local_env)++ctx.(ctx_global_env)) name in
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
      let ctx' := ergo_context_update_local_env ctx n v' in
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

      (* RIP modularity *)
  | ENew nr rs =>
    match nr with
      (* TODO this is wrong, they should be flipped... >sigh< *)
    | ENames.AbsoluteRef n => efailure (SystemError "Name resolution did not resolve name.")
    | ENames.RelativeRef _ n =>
      match
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
      with
      | Failure _ _ f => efailure f
      | Success _ _ r => esuccess (dbrand (n::nil) r)
      end
    end

  | ECallFun fn args =>
    match lookup String.string_dec ctx.(ctx_function_list) fn with
    | Some fn' =>
      let lam := fn'.(function_lambda) in
      let nms := lam.(lambda_params) in
      let bod := lam.(lambda_body) in
      esuccess dunit
    | None => efailure (RuntimeError ("Function " ++ fn ++ " not found."))
    end
  | EMatch e pes f => TODO
  | EForeach ls whr f => TODO
  | ELiftError e1 e2 => TODO
  end.

Fixpoint ergo_eval_stmt (ctx : ergo_context) (stmt : ergo_stmt) : eresult (ergo_context * ergo_data) :=
       match stmt with
       | SReturn expr => TODO
       | SFunReturn expr => TODO
       | SThrow expr => TODO
       | SCallClause name args => TODO
       | SSetState expr stmt' => TODO
       | SEmit expr stmt' => TODO
       | SLet name type val stmt' => TODO
       | SIf c t f => TODO
       | SEnforce e f stmt' => TODO
       | SMatch e cls stmt' => TODO
       end.

Fixpoint ergo_eval_decl (ctx : ergo_context) (decl : ergo_declaration) : eresult (ergo_context * option ergo_data) :=
  match decl with
  | EType cto => esuccess (ctx, None)
  | EExpr e =>
    match ergo_eval_expr ctx e with
    | Success _ _ r => esuccess (ctx, Some r)
    | Failure _ _ f => efailure f
    end
  | EGlobal n e =>
    match ergo_eval_expr ctx e with
    | Success _ _ r =>
      esuccess (ergo_context_update_global_env ctx n r, Some r)
    | Failure _ _ f => efailure f
    end
  | EFunc f => TODO
  | EContract c => TODO
  end.

Definition ergo_eval_module (ctx : ergo_context) (module : ergo_module) : eresult (ergo_context * option ergo_data) :=
  fold_left
    (fun prev_ctx d =>
       match prev_ctx with
       | Failure _ _ f => efailure f
       | Success _ _ (ctx', _) =>
         match ergo_eval_decl ctx' d with
         | Failure _ _ f => efailure f
         | s => s
         end
       end)
  module.(module_declarations) (esuccess (ctx, None)).

Definition ergo_string_of_error (err : eerror) : string :=
  match err with
  | SystemError s => "System Error: " ++ s
  | ParseError p => "Parse Error (?!)"
  | CompilationError s => "Compilation Error: " ++ s
  | TypeError s => "Type Error: " ++ s
  | RuntimeError s => "Runtime Error: " ++ s
  end.

Definition ergo_string_of_result (result : eresult (ergo_context * option ergo_data)) : string :=
  match result with
  | Success _ _ (ctx, None) => "[ok]"
  | Success _ _ (ctx, Some d) => dataToString d
  | Failure _ _ f => ergo_string_of_error f
  end.

Definition ergo_maybe_update_context (ctx : ergo_context) (result : eresult (ergo_context * option ergo_data)) : ergo_context :=
  match result with
  | Success _ _ (ctx', Some d) => ctx'
  | _ => ctx
  end.


End ErgoEval.

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