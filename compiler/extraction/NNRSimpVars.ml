open CoqLibAdd
open Datatypes
open ForeignRuntime
open List0
open NNRSimp
open Var

(** val nnrs_imp_expr_free_vars :
    foreign_runtime -> nnrs_imp_expr -> var list **)

let rec nnrs_imp_expr_free_vars fruntime = function
| NNRSimpVar v -> v :: []
| NNRSimpBinop (_, e_UU2081_, e_UU2082_) ->
  app (nnrs_imp_expr_free_vars fruntime e_UU2081_)
    (nnrs_imp_expr_free_vars fruntime e_UU2082_)
| NNRSimpUnop (_, e_UU2081_) -> nnrs_imp_expr_free_vars fruntime e_UU2081_
| NNRSimpGroupBy (_, _, e_UU2081_) ->
  nnrs_imp_expr_free_vars fruntime e_UU2081_
| _ -> []

(** val nnrs_imp_stmt_free_vars :
    foreign_runtime -> nnrs_imp_stmt -> var list **)

let rec nnrs_imp_stmt_free_vars fruntime = function
| NNRSimpSkip -> []
| NNRSimpSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_imp_stmt_free_vars fruntime s_UU2081_)
    (nnrs_imp_stmt_free_vars fruntime s_UU2082_)
| NNRSimpAssign (v, e) -> v :: (nnrs_imp_expr_free_vars fruntime e)
| NNRSimpLet (v, eo, s_UU2080_) ->
  app
    (match eo with
     | Some e -> nnrs_imp_expr_free_vars fruntime e
     | None -> [])
    (remove string_eqdec v (nnrs_imp_stmt_free_vars fruntime s_UU2080_))
| NNRSimpFor (v, e, s_UU2080_) ->
  app (nnrs_imp_expr_free_vars fruntime e)
    (remove string_eqdec v (nnrs_imp_stmt_free_vars fruntime s_UU2080_))
| NNRSimpIf (e, s_UU2081_, s_UU2082_) ->
  app (nnrs_imp_expr_free_vars fruntime e)
    (app (nnrs_imp_stmt_free_vars fruntime s_UU2081_)
      (nnrs_imp_stmt_free_vars fruntime s_UU2082_))
| NNRSimpEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
  app (nnrs_imp_expr_free_vars fruntime e)
    (app
      (remove string_eqdec x_UU2081_
        (nnrs_imp_stmt_free_vars fruntime s_UU2081_))
      (remove string_eqdec x_UU2082_
        (nnrs_imp_stmt_free_vars fruntime s_UU2082_)))

(** val nnrs_imp_stmt_bound_vars :
    foreign_runtime -> nnrs_imp_stmt -> var list **)

let rec nnrs_imp_stmt_bound_vars fruntime = function
| NNRSimpSeq (s_UU2081_, s_UU2082_) ->
  app (nnrs_imp_stmt_bound_vars fruntime s_UU2081_)
    (nnrs_imp_stmt_bound_vars fruntime s_UU2082_)
| NNRSimpLet (v, _, s_UU2080_) ->
  v :: (nnrs_imp_stmt_bound_vars fruntime s_UU2080_)
| NNRSimpFor (v, _, s_UU2080_) ->
  v :: (nnrs_imp_stmt_bound_vars fruntime s_UU2080_)
| NNRSimpIf (_, s_UU2081_, s_UU2082_) ->
  app (nnrs_imp_stmt_bound_vars fruntime s_UU2081_)
    (nnrs_imp_stmt_bound_vars fruntime s_UU2082_)
| NNRSimpEither (_, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
  x_UU2081_ :: (app (nnrs_imp_stmt_bound_vars fruntime s_UU2081_)
                 (x_UU2082_ :: (nnrs_imp_stmt_bound_vars fruntime s_UU2082_)))
| _ -> []
