open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open List0
open NNRS
open Var

(** val nnrs_expr_free_vars : foreign_runtime -> nnrs_expr -> var list **)

let rec nnrs_expr_free_vars fruntime = function
| NNRSVar v -> v :: []
| NNRSBinop (_, e_UU2081_, e_UU2082_) ->
  app (nnrs_expr_free_vars fruntime e_UU2081_)
    (nnrs_expr_free_vars fruntime e_UU2082_)
| NNRSUnop (_, e_UU2081_) -> nnrs_expr_free_vars fruntime e_UU2081_
| NNRSGroupBy (_, _, e_UU2081_) -> nnrs_expr_free_vars fruntime e_UU2081_
| _ -> []

(** val nnrs_stmt_free_env_vars : foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_free_env_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_env_vars fruntime s_UU2081_)
    (nnrs_stmt_free_env_vars fruntime s_UU2082_)
| NNRSLet (v, e, s_UU2080_) ->
  app (nnrs_expr_free_vars fruntime e)
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_env_vars fruntime s_UU2080_))
| NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_env_vars fruntime s_UU2081_)
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_env_vars fruntime s_UU2082_))
| NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_env_vars fruntime s_UU2081_)
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_env_vars fruntime s_UU2082_))
| NNRSAssign (_, e) -> nnrs_expr_free_vars fruntime e
| NNRSPush (_, e) -> nnrs_expr_free_vars fruntime e
| NNRSFor (v, e, s_UU2080_) ->
  app (nnrs_expr_free_vars fruntime e)
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_env_vars fruntime s_UU2080_))
| NNRSIf (e, s_UU2081_, s_UU2082_) ->
  app (nnrs_expr_free_vars fruntime e)
    (app (nnrs_stmt_free_env_vars fruntime s_UU2081_)
      (nnrs_stmt_free_env_vars fruntime s_UU2082_))
| NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
  app (nnrs_expr_free_vars fruntime e)
    (app
      (remove (equiv_dec string_eqdec) x_UU2081_
        (nnrs_stmt_free_env_vars fruntime s_UU2081_))
      (remove (equiv_dec string_eqdec) x_UU2082_
        (nnrs_stmt_free_env_vars fruntime s_UU2082_)))

(** val nnrs_stmt_free_mcenv_vars :
    foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_free_mcenv_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_)
| NNRSLet (_, _, s_UU2080_) -> nnrs_stmt_free_mcenv_vars fruntime s_UU2080_
| NNRSLetMut (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_)
| NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
  app
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_))
    (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_)
| NNRSAssign (_, _) -> []
| NNRSPush (v, _) -> v :: []
| NNRSFor (_, _, s_UU2080_) -> nnrs_stmt_free_mcenv_vars fruntime s_UU2080_
| NNRSIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_)
| NNRSEither (_, _, s_UU2081_, _, s_UU2082_) ->
  app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_)

(** val nnrs_stmt_free_mdenv_vars :
    foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_free_mdenv_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_)
| NNRSLet (_, _, s_UU2080_) -> nnrs_stmt_free_mdenv_vars fruntime s_UU2080_
| NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
  app
    (remove (equiv_dec string_eqdec) v
      (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_))
    (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_)
| NNRSLetMutColl (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_)
| NNRSAssign (v, _) -> v :: []
| NNRSPush (_, _) -> []
| NNRSFor (_, _, s_UU2080_) -> nnrs_stmt_free_mdenv_vars fruntime s_UU2080_
| NNRSIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_)
| NNRSEither (_, _, s_UU2081_, _, s_UU2082_) ->
  app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_)

(** val nnrs_stmt_bound_env_vars :
    foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_bound_env_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_env_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_env_vars fruntime s_UU2082_)
| NNRSLet (v, _, s_UU2080_) ->
  v :: (nnrs_stmt_bound_env_vars fruntime s_UU2080_)
| NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
  v :: (app (nnrs_stmt_bound_env_vars fruntime s_UU2081_)
         (nnrs_stmt_bound_env_vars fruntime s_UU2082_))
| NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
  v :: (app (nnrs_stmt_bound_env_vars fruntime s_UU2081_)
         (nnrs_stmt_bound_env_vars fruntime s_UU2082_))
| NNRSFor (v, _, s_UU2080_) ->
  v :: (nnrs_stmt_bound_env_vars fruntime s_UU2080_)
| NNRSIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_env_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_env_vars fruntime s_UU2082_)
| NNRSEither (_, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
  x_UU2081_ :: (x_UU2082_ :: (app
                               (nnrs_stmt_bound_env_vars fruntime s_UU2081_)
                               (nnrs_stmt_bound_env_vars fruntime s_UU2082_)))
| _ -> []

(** val nnrs_stmt_bound_mcenv_vars :
    foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_bound_mcenv_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_)
| NNRSLet (_, _, s_UU2080_) -> nnrs_stmt_bound_mcenv_vars fruntime s_UU2080_
| NNRSLetMut (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_)
| NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
  v :: (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_)
         (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_))
| NNRSFor (_, _, s_UU2080_) -> nnrs_stmt_bound_mcenv_vars fruntime s_UU2080_
| NNRSIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_)
| NNRSEither (_, _, s_UU2081_, _, s_UU2082_) ->
  app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_)
| _ -> []

(** val nnrs_stmt_bound_mdenv_vars :
    foreign_runtime -> nnrs_stmt -> var list **)

let rec nnrs_stmt_bound_mdenv_vars fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_)
| NNRSLet (_, _, s_UU2080_) -> nnrs_stmt_bound_mdenv_vars fruntime s_UU2080_
| NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
  v :: (app (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_)
         (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_))
| NNRSLetMutColl (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_)
| NNRSFor (_, _, s_UU2080_) -> nnrs_stmt_bound_mdenv_vars fruntime s_UU2080_
| NNRSIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_)
| NNRSEither (_, _, s_UU2081_, _, s_UU2082_) ->
  app (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_)
    (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_)
| _ -> []
