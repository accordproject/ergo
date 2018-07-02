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

Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.ErgoNameResolve.
Require Import Common.Utils.EResult.

Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Translation.CTOtoErgo.

Require Ergo.
Require Import Ergo.
Definition ergo_data := ErgoData.data.
Definition ergo_expr := Ergo.laergo_expr.
Definition ergo_stmt := Ergo.laergo_stmt.
Definition ergo_function := Ergo.laergo_function.
Definition ergo_clause := Ergo.laergo_clause.
Definition ergo_contract := Ergo.laergo_contract.
Definition ergo_declaration := Ergo.laergo_declaration.
Definition ergo_module := Ergo.laergo_module.

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
           (loc : location)
           (body : ergo_expr)
           (args : list (string * ergo_expr)) : ergo_expr :=
    match args with
    | nil => body
    | (n,v)::rest => ELet loc n None v (ergo_letify_function' loc body rest)
    end.

  Definition ergo_letify_function (fn : ergo_function) (args : list ergo_expr) :=
    match fn.(function_body) with
    | None => TODO
    | Some (SFunReturn loc body) =>
      match zip (map fst (fn.(function_sig).(type_signature_params))) args with
      | Some args' => esuccess (ergo_letify_function' fn.(function_annot) body args')
      | None => efailure (CompilationError fn.(function_annot) ("Wrong number of arguments for "%string ++ fn.(function_name))%string)
      end
    | _ =>
      efailure
        (CompilationError
           fn.(function_annot) (("Function "%string) ++ fn.(function_name) ++ (" is bad."%string)))
    end.

  Fixpoint ergo_inline_expr
           (ctx : ergo_context)
           (expr : ergo_expr) : eresult ergo_expr :=
    match expr with
    | EThisContract _ => esuccess expr
    | EThisClause _ => esuccess expr
    | EThisState _ => esuccess expr
    | EVar _ _ => esuccess expr
    | EConst _ _ => esuccess expr
    | EArray loc a =>
      elift (EArray loc)
            (fold_left
               (fun ls na =>
                  elift2 postpend ls (ergo_inline_expr ctx na))
               a (esuccess nil))
    | EUnaryOp loc o e => elift (EUnaryOp loc o) (ergo_inline_expr ctx e)
    | EBinaryOp loc o e1 e2 =>
      elift2 (EBinaryOp loc o) (ergo_inline_expr ctx e1) (ergo_inline_expr ctx e2)
    | EIf loc c t f =>
      elift3 (EIf loc)
             (ergo_inline_expr ctx c)
             (ergo_inline_expr ctx t)
             (ergo_inline_expr ctx f)
    | ELet loc n t v b =>
      elift2 (fun v' b' => (ELet loc) n t v' b')
             (ergo_inline_expr ctx v)
             (ergo_inline_expr ctx b)
    | ERecord loc rs =>
      elift (ERecord loc)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_expr ctx (snd nr))))
               rs (esuccess nil))
    | ENew loc n rs =>
      elift (ENew loc n)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_expr ctx (snd nr))))
               rs (esuccess nil))
    | ECallFun loc fn args =>
      match lookup String.string_dec ctx.(ctx_function_env) fn with
      | Some fn' =>
        eolift (ergo_letify_function fn')
               (fold_left (fun ls nv =>
                             elift2 postpend ls (ergo_inline_expr ctx nv))
                          args (esuccess nil))
      | None => efailure (CompilationError loc ("Function " ++ fn ++ " not found.")%string)
      end
    | EMatch _ _ _ _ => TODO
 
    | EForeach loc rs whr fn =>
      let singleton := fun x => EArray loc (x::nil) in
      let base := 
        match whr with
        | None => elift singleton (ergo_inline_expr ctx fn)
        | Some whr' =>
          elift3 (EIf loc)
                 (ergo_inline_expr ctx whr')
                 (elift singleton (ergo_inline_expr ctx fn))
                 (esuccess (EArray loc nil))
        end
      in
      fold_right
        (fun lay ker =>
           elift
             (EUnaryOp loc OpFlatten)
             (elift3 (EForeach loc)
                     (elift (fun v' => (fst lay, v')::nil) (ergo_inline_expr ctx (snd lay)))
                     (match whr with
                      | None => esuccess None
                      | Some x => elift Some (ergo_inline_expr ctx x)
                      end)
                     ker))
        base rs
 
    end.

  Fixpoint ergo_inline_globals
           (ctx : ergo_context)
           (expr : ergo_expr) : eresult ergo_expr :=
    match expr with
    | EThisContract _ => esuccess expr
    | EThisClause _ => esuccess expr
    | EThisState _ => esuccess expr
    | EVar loc name =>
      match lookup String.string_dec (ctx.(ctx_local_env)) name with
      | Some _ => esuccess expr
      | None =>
        match lookup String.string_dec (ctx.(ctx_global_env)) name with
        | Some val => esuccess (EConst loc val)
        | None => esuccess expr
        end
      end
    | EConst _ _ => esuccess expr
    | EArray loc a =>
      elift (EArray loc)
            (fold_left
               (fun ls na =>
                  elift2 postpend ls (ergo_inline_globals ctx na))
               a (esuccess nil))
    | EUnaryOp loc o e => elift (EUnaryOp loc o) (ergo_inline_globals ctx e)
    | EBinaryOp loc o e1 e2 =>
      elift2 (EBinaryOp loc o) (ergo_inline_globals ctx e1) (ergo_inline_globals ctx e2)
    | EIf loc c t f =>
      elift3 (EIf loc)
             (ergo_inline_globals ctx c)
             (ergo_inline_globals ctx t)
             (ergo_inline_globals ctx f)
    | ELet loc n t v b =>
      elift2 (fun v' b' => (ELet loc) n t v' b')
             (ergo_inline_globals ctx v)
             (ergo_inline_globals (ergo_ctx_update_local_env ctx n dunit) b)
    | ERecord loc rs =>
      elift (ERecord loc)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctx (snd nr))))
               rs (esuccess nil))
    | ENew loc n rs =>
      elift (ENew loc n)
            (fold_left
               (fun ls nr =>
                  elift2 postpend ls
                         (elift (fun x => (fst nr, x)) (ergo_inline_globals ctx (snd nr))))
               rs (esuccess nil))
    | ECallFun loc fn args =>
        elift (ECallFun loc fn)
              (fold_left
                 (fun ls nv =>
                    elift2 postpend ls (ergo_inline_globals ctx nv))
                 args (esuccess nil))
    | EMatch _ _ _ _ => TODO
    | EForeach loc rs whr fn =>
      elift3 (EForeach loc)
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
    end.

  Definition ergo_inline_function
           (ctx : ergo_context)
           (fn : ergo_function) : eresult ergo_function :=
    match fn.(function_body) with
    | None => TODO
    | Some (SFunReturn loc expr) =>
      match eolift (ergo_inline_expr ctx) (ergo_inline_globals ctx expr) with
        | Success _ _ new_body =>
          esuccess (mkFunc loc
                           fn.(function_name)
                                fn.(function_sig)
                                (Some (SFunReturn loc new_body)))
        | Failure _ _ f => efailure f
      end
    | _ => efailure (CompilationError fn.(function_annot) ("Function "++fn.(function_name)++" is bad!!!")%string)
    end.

Fixpoint ergo_eval_expr (ctx : ergo_context) (expr : ergo_expr) : eresult ergo_data :=
  match expr with
  | EThisContract _ => esuccess ctx.(ctx_this_contract)
  | EThisClause _ => esuccess ctx.(ctx_this_clause)
  | EThisState _ => esuccess ctx.(ctx_this_state)
  | EVar loc name =>
    let opt := lookup String.string_dec (ctx.(ctx_local_env)++ctx.(ctx_global_env)) name in
    eresult_of_option opt (RuntimeError loc ("Variable not found: " ++ name)%string)
  | EConst loc d => esuccess d

  | EArray loc es =>
    fold_left
      (fun ls new =>
         match ls with
         | Success _ _ (dcoll ls') =>
           match ergo_eval_expr ctx new with
           | Success _ _ new' => esuccess (dcoll (ls' ++ (new'::nil)))
           | Failure _ _ f => efailure f
           end
         | Success _ _ _ => efailure (RuntimeError loc "This should never happen.")
         | Failure _ _ f => efailure f
         end)
      es (esuccess (dcoll nil))

  | EUnaryOp loc o e  =>
    match ergo_eval_expr ctx e with
    | Success _ _ e' =>
      (* TODO this takes a type hierarchy as a list of string * strings. *)
      match ergo_unary_eval nil o e' with
      | Some r => esuccess r
      | None => efailure (RuntimeError loc "Unary operation failed.")
      end
    | Failure _ _ f => efailure f
    end
    
  | EBinaryOp loc o e1 e2 =>
    match ergo_eval_expr ctx e1 with
    | Success _ _ e1' =>
      match ergo_eval_expr ctx e2 with
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
    match ergo_eval_expr ctx c with
    | Success _ _ (dbool true) => ergo_eval_expr ctx t
    | Success _ _ (dbool false) => ergo_eval_expr ctx f
    | Success _ _ _ => efailure (RuntimeError loc "'If' condition not boolean.")
    | Failure _ _ f => efailure f
    end

  | ELet loc n t v e =>
    match ergo_eval_expr ctx v with
    | Success _ _ v' =>
      let ctx' := ergo_ctx_update_local_env ctx n v' in
      ergo_eval_expr ctx' e
    | Failure _ _ f => efailure f
    end

  | ERecord loc rs =>
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
             match ergo_eval_expr ctx value with
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

  | ECallFun loc fn args => efailure (CompilationError loc "You forgot to inline a call...")

  | EMatch loc e pes f => TODO

  | EForeach loc rs whr fn =>
    match rs with
    | (name, arr)::nil =>
      match ergo_eval_expr ctx arr with
      | Failure _ _ f => efailure f
      | Success _ _ (dcoll arr') =>
        (elift dcoll)
          (emaplift
             (fun elt => ergo_eval_expr (ergo_ctx_update_local_env ctx name elt) fn)
             arr')
      | Success _ _ _ => efailure (RuntimeError loc "Foreach needs to be called on an array")
      end
    | _ => efailure (RuntimeError loc "Failed to inline foreach")
    end

  end.

Fixpoint ergo_eval_stmt (ctx : ergo_context) (stmt : ergo_stmt) : eresult (ergo_context * option ergo_data) :=
       match stmt with
       | SReturn _ expr =>
         elift (fun x => (ctx, Some x))
               (eolift (ergo_eval_expr ctx) (ergo_inline_expr ctx expr))
       | SFunReturn _ expr => TODO
       | SThrow _ expr => TODO
       | SCallClause _ name args => TODO
       | SSetState _ expr stmt' => TODO
       | SEmit _ expr stmt' => TODO
       | SLet _ name type val stmt' => TODO
       | SIf _ c t f => TODO
       | SEnforce _ e f stmt' => TODO
       | SMatch _ e cls stmt' => TODO
       end.

Fixpoint ergo_eval_decl (ctx : ergo_context) (decl : ergo_declaration) : eresult (ergo_context * option ergo_data) :=
  match decl with
  | DType _ cto => esuccess (ctx, None)
  | DStmt _ stmt => ergo_eval_stmt ctx stmt
                            (*
  | DExpr _ e =>
    match eolift (ergo_eval_expr ctx) (ergo_inline_expr ctx e) with
    | Success _ _ r => esuccess (ctx, Some r)
    | Failure _ _ f => efailure f
    end
*)
  | DConstant _ n e =>
    match eolift (ergo_eval_expr ctx) (ergo_inline_expr ctx e) with
    | Success _ _ r =>
      esuccess (ergo_ctx_update_global_env ctx n r, None)
    | Failure _ _ f => efailure f
    end
  | DFunc _ fn =>
    elift (fun fn' => (ergo_ctx_update_function_env ctx fn'.(function_name) fn', None))
          (ergo_inline_function ctx fn)
  | DContract _ c => TODO
  end.

Definition ergo_eval_module
           (ctos:list cto_package)
           (ml:list lrergo_module)
           (ctx : ergo_context)
           (module : lrergo_module)
  : eresult (ergo_context * option ergo_data) :=

  let mctos := map cto_package_to_ergo_module ctos in
  let nsctxt := namespace_ctxt_of_ergo_modules (mctos ++ ml ++ (module::nil)) in

  match (resolve_ergo_single_module nsctxt module) with
  | Success _ _ mdl =>
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
      mdl.(module_declarations) 
          (esuccess (ctx, None))
  | Failure _ _ f => efailure f
  end.

(* Require Import Qcert.Basic.Util.Digits. *)
Definition ergo_string_of_location_point (lp : location_point) : string :=
  (toString lp.(line)) ++ ":" ++ (toString lp.(column)).

Definition ergo_string_of_location (loc : location) : string :=
  let file :=
      match loc.(loc_file) with
      | Some f => (f ++ " ")%string
      | None => ""%string
      end
  in
  file ++
  (ergo_string_of_location_point loc.(loc_start)) ++ "-" ++
  (ergo_string_of_location_point loc.(loc_end)).

Definition ergo_format_error (name : string) (loc : location) (msg : string) :=
  (name ++ " at " ++ (ergo_string_of_location loc) ++ " '" ++ msg ++ "'")%string.

Definition ergo_string_of_error (err : eerror) : string :=
  match err with
  | SystemError s => "System error: " ++ s
  | ParseError loc msg => ergo_format_error "Parse error" loc msg
  | CompilationError loc msg => ergo_format_error "Compilation error" loc msg
  | TypeError loc msg => ergo_format_error "Type error" loc msg
  | RuntimeError loc msg => ergo_format_error "Runtime error" loc msg
  end.

Definition ergo_string_of_result (result : eresult (ergo_context * option ergo_data)) : string :=
  match result with
  | Success _ _ (ctx, None) => ""
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
