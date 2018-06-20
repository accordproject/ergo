Require Import Ergo.
Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import Common.Utils.EResult.

Definition ergo_data := ErgoData.data.

Section ErgoEval.

  Record ergo_context :=
    mkContext
      { function_list : list ergo_function;
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

  | ERecord rs => esuccess dunit
  | ENew nr vs => esuccess dunit
  | ECallFun f es => esuccess dunit
  | EMatch e pes f => esuccess dunit
  | EForeach ls whr f => esuccess dunit
  | ELiftError e1 e2 => esuccess dunit
  end.

Definition easy := EConst (dnat 0).

Compute (ergo_eval_expr ergo_empty_context easy). (* Compute = Eval vm_compute in *)

End ErgoEval.