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

(* TODO: Fix all the folds. There is currently an even number of reversings... >_< *)

Require Import Ergo.
Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import Common.Utils.EResult.

Definition ergo_data := ErgoData.data.

Section ErgoEval.

  Record ergo_context :=
    mkContext
      { ctx_function_env : list (string * ergo_function);
        ctx_clause_env : list (string * ergo_clause);
        ctx_contract_env : list (string * ergo_contract);
        ctx_global_env : list (string * ergo_data);
        ctx_local_env : list (string * ergo_data);
        ctx_this_clause : ergo_data;
        ctx_this_contract : ergo_data;
        ctx_this_state : ergo_data;
        ctx_this_emit : ergo_data;
        }.

  Definition postpend {A : Set} (ls : list A) (a : A) : list A :=
    ls ++ (a :: nil).

  Definition ergo_empty_context :=
    mkContext nil nil nil nil nil dunit dunit dunit dunit.

  Definition TODO {A : Set} : eresult A := efailure (SystemError "Feature not implemented.").

  Definition ergo_unary_eval := ErgoOps.Unary.eval.
  Definition ergo_binary_eval := ErgoOps.Binary.eval.

  Definition ergo_ctx_update_function_env (ctx : ergo_context) (name : string) (value : ergo_function) : ergo_context :=
    mkContext ((name, value)::ctx.(ctx_function_env))
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              ctx.(ctx_local_env)
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_update_global_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              ((name, value)::ctx.(ctx_global_env))
              (ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_update_local_env (ctx : ergo_context) (name : string) (value : ergo_data) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              ((name, value)::ctx.(ctx_local_env))
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Definition ergo_ctx_set_local_env (ctx : ergo_context) (new_local_env : list (string * ergo_data)) : ergo_context :=
    mkContext ctx.(ctx_function_env)
              ctx.(ctx_clause_env)
              ctx.(ctx_contract_env)
              (ctx.(ctx_global_env))
              new_local_env
              ctx.(ctx_this_clause)
              ctx.(ctx_this_contract)
              ctx.(ctx_this_state)
              ctx.(ctx_this_emit).

  Fixpoint ergo_letify_function'
           (body : ergo_expr)
           (args : list (string * ergo_expr)) : ergo_expr :=
    match args with
    | nil => body
    | (n,v)::rest => ELet n None v (ergo_letify_function' body rest)
    end.

  Definition ergo_letify_function (fn : ergo_function) (args : list ergo_expr) :=
    match fn.(function_lambda).(lambda_body) with
    | SFunReturn body =>
      match zip (map fst (fn.(function_lambda).(lambda_params))) args with
      | Some args' => esuccess (ergo_letify_function' body args')
      | None => efailure (CompilationError ("Wrong number of arguments for " ++ fn.(function_name)))
      end
    | _ => efailure (CompilationError ("Function " ++ fn.(function_name) ++ " is bad."))
    end.

  Fixpoint ergo_inline_expr
           (ctx : ergo_context)
           (expr : ergo_expr) : eresult ergo_expr :=
    match expr with
    | EThisContract => esuccess expr
    | EThisClause => esuccess expr
    | EThisState => esuccess expr
    | EVar _ => esuccess expr
    | EConst _ => esuccess expr
    | EArray a =>
      elift EArray
            (fold_left
               (fun ls na =>
                  elift2 postpend ls (ergo_inline_expr ctx na))
               a (esuccess nil))
    | EUnaryOp o e => elift (EUnaryOp o) (ergo_inline_expr ctx e)
    | EBinaryOp o e1 e2 =>
      elift2 (EBinaryOp o) (ergo_inline_expr ctx e1) (ergo_inline_expr ctx e2)
    | EIf c t f =>
      elift3 EIf
             (ergo_inline_expr ctx c)
             (ergo_inline_expr ctx t)
             (ergo_inline_expr ctx f)
    | ELet n t v b =>
      elift2 (fun v' b' => ELet n t v' b')
             (ergo_inline_expr ctx v)
             (ergo_inline_expr ctx b)
    | ERecord rs =>
      elift ERecord
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_expr ctx (snd nr))))
               rs (esuccess nil))
    | ENew n rs =>
      elift (ENew n)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_expr ctx (snd nr))))
               rs (esuccess nil))
    | ECallFun fn args =>
      match lookup String.string_dec ctx.(ctx_function_env) fn with
      | Some fn' =>
        eolift (ergo_letify_function fn')
               (fold_left (fun ls nv =>
                             elift2 postpend ls (ergo_inline_expr ctx nv))
                          args (esuccess nil))
      | None => efailure (CompilationError ("Function " ++ fn ++ " not found."))
      end
    | EMatch _ _ _ => TODO
 
    | EForeach rs whr fn =>
      let singleton := fun x => EArray (x::nil) in
      let base := 
        match whr with
        | None => elift singleton (ergo_inline_expr ctx fn)
        | Some whr' =>
          elift3 EIf
                 (ergo_inline_expr ctx whr')
                 (elift singleton (ergo_inline_expr ctx fn))
                 (esuccess (EArray nil))
        end
      in
      fold_right
        (fun lay ker =>
           elift (EUnaryOp OpFlatten)
                 (
           elift3 EForeach
                  (elift (fun v' => (fst lay, v')::nil) (ergo_inline_expr ctx (snd lay)))
                  (match whr with
                   | None => esuccess None
                   | Some x => elift Some (ergo_inline_expr ctx x)
                   end)
                  ker
                  )
        )
        base rs
 
    | ELiftError _ _ => TODO
    end.

  Fixpoint ergo_inline_globals
           (ctx : ergo_context)
           (expr : ergo_expr) : eresult ergo_expr :=
    match expr with
    | EThisContract => esuccess expr
    | EThisClause => esuccess expr
    | EThisState => esuccess expr
    | EVar name =>
      match lookup String.string_dec (ctx.(ctx_local_env)) name with
      | Some _ => esuccess expr
      | None =>
        match lookup String.string_dec (ctx.(ctx_global_env)) name with
        | Some val => esuccess (EConst val)
        | None => esuccess expr
        end
      end
    | EConst _ => esuccess expr
    | EArray a =>
      elift EArray
            (fold_left
               (fun ls na =>
                  elift2 postpend ls (ergo_inline_globals ctx na))
               a (esuccess nil))
    | EUnaryOp o e => elift (EUnaryOp o) (ergo_inline_globals ctx e)
    | EBinaryOp o e1 e2 =>
      elift2 (EBinaryOp o) (ergo_inline_globals ctx e1) (ergo_inline_globals ctx e2)
    | EIf c t f =>
      elift3 EIf
             (ergo_inline_globals ctx c)
             (ergo_inline_globals ctx t)
             (ergo_inline_globals ctx f)
    | ELet n t v b =>
      elift2 (fun v' b' => ELet n t v' b')
             (ergo_inline_globals ctx v)
             (ergo_inline_globals (ergo_ctx_update_local_env ctx n dunit) b)
    | ERecord rs =>
      elift ERecord
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctx (snd nr))))
               rs (esuccess nil))
    | ENew n rs =>
      elift (ENew n)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctx (snd nr))))
               rs (esuccess nil))
    | ECallFun fn args =>
        elift (ECallFun fn)
              (fold_left
                 (fun ls nv =>
                    elift2 postpend ls (ergo_inline_globals ctx nv))
                 args (esuccess nil))
    | EMatch _ _ _ => TODO
    | EForeach rs whr fn =>
      elift3 EForeach
             (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctx (snd nr))))
               rs (esuccess nil))
             (match whr with
              | Some whr' => (elift Some) (ergo_inline_globals ctx whr')
              | None => esuccess None
              end)
             (ergo_inline_globals ctx fn)
    | ELiftError _ _ => TODO
    end.

  Definition ergo_inline_function
           (ctx : ergo_context)
           (fn : ergo_function) : eresult ergo_function :=
    match fn.(function_lambda).(lambda_body) with
    | SFunReturn expr =>
      match eolift (ergo_inline_expr ctx) (ergo_inline_globals ctx expr) with
        | Success _ _ new_body =>
          esuccess (mkFunc fn.(function_name)
                    (mkLambda fn.(function_lambda).(lambda_params)
                              fn.(function_lambda).(lambda_output)
                              fn.(function_lambda).(lambda_throws)
                              fn.(function_lambda).(lambda_emits)
                              (SFunReturn new_body)))
        | Failure _ _ f => efailure f
      end
    | _ => efailure (CompilationError ("Function "++fn.(function_name)++" is bad!!!"))
    end.

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
      let ctx' := ergo_ctx_update_local_env ctx n v' in
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

  | ECallFun fn args => efailure (CompilationError "You forgot to inline a call...")

  | EMatch e pes f => TODO

  | EForeach rs whr fn =>
    match rs with
    | (name, arr)::nil =>
      match ergo_eval_expr ctx arr with
      | Failure _ _ f => efailure f
      | Success _ _ (dcoll arr') =>
        (elift dcoll)
          (emaplift
             (fun elt => ergo_eval_expr (ergo_ctx_update_local_env ctx name elt) fn)
             arr')
      | Success _ _ _ => efailure (RuntimeError "Foreach needs to be called on an array")
      end
    | _ => efailure (RuntimeError "Failed to inline foreach")
    end

  | ELiftError e1 e2 => TODO (* This isn't a thing though so we're okay :) *)
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
    match eolift (ergo_eval_expr ctx) (ergo_inline_expr ctx e) with
    | Success _ _ r => esuccess (ctx, Some r)
    | Failure _ _ f => efailure f
    end
  | EGlobal n e =>
    match eolift (ergo_eval_expr ctx) (ergo_inline_expr ctx e) with
    | Success _ _ r =>
      esuccess (ergo_ctx_update_global_env ctx n r, None)
    | Failure _ _ f => efailure f
    end
  | EFunc fn =>
    elift (fun fn' => (ergo_ctx_update_function_env ctx fn'.(function_name) fn', None))
          (ergo_inline_function ctx fn)
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
  | Success _ _ (ctx, None) => "lol ok"
  | Success _ _ (ctx, Some d) => (*dataToString d*) ErgoData.data_to_json_string ""%string d
  | Failure _ _ f => ergo_string_of_error f
  end.

Definition ergo_maybe_update_context (ctx : ergo_context) (result : eresult (ergo_context * option ergo_data)) : ergo_context :=
  match result with
  | Success _ _ (ctx', _) => ctx'
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
