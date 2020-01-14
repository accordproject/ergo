open CoqLibAdd
open EquivDec
open ForeignRuntime
open NNRS
open Var

(** val nnrs_stmt_rename_mc :
    foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt **)

let rec nnrs_stmt_rename_mc fruntime s oldvar newvar =
  match s with
  | NNRSSeq (s_UU2081_, s_UU2082_) ->
    NNRSSeq ((nnrs_stmt_rename_mc fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_mc fruntime s_UU2082_ oldvar newvar))
  | NNRSLet (v, e, s_UU2080_) ->
    NNRSLet (v, e, (nnrs_stmt_rename_mc fruntime s_UU2080_ oldvar newvar))
  | NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMut (v, (nnrs_stmt_rename_mc fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_mc fruntime s_UU2082_ oldvar newvar))
  | NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMutColl (v,
      (if equiv_dec string_eqdec v oldvar
       then s_UU2081_
       else nnrs_stmt_rename_mc fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_mc fruntime s_UU2082_ oldvar newvar))
  | NNRSAssign (v, e) -> NNRSAssign (v, e)
  | NNRSPush (v, e) ->
    NNRSPush ((if equiv_dec string_eqdec v oldvar then newvar else v), e)
  | NNRSFor (v, e, s_UU2080_) ->
    NNRSFor (v, e, (nnrs_stmt_rename_mc fruntime s_UU2080_ oldvar newvar))
  | NNRSIf (e, s_UU2081_, s_UU2082_) ->
    NNRSIf (e, (nnrs_stmt_rename_mc fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_mc fruntime s_UU2082_ oldvar newvar))
  | NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
    NNRSEither (e, x_UU2081_,
      (nnrs_stmt_rename_mc fruntime s_UU2081_ oldvar newvar), x_UU2082_,
      (nnrs_stmt_rename_mc fruntime s_UU2082_ oldvar newvar))

(** val nnrs_stmt_rename_md :
    foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt **)

let rec nnrs_stmt_rename_md fruntime s oldvar newvar =
  match s with
  | NNRSSeq (s_UU2081_, s_UU2082_) ->
    NNRSSeq ((nnrs_stmt_rename_md fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_md fruntime s_UU2082_ oldvar newvar))
  | NNRSLet (v, e, s_UU2080_) ->
    NNRSLet (v, e, (nnrs_stmt_rename_md fruntime s_UU2080_ oldvar newvar))
  | NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMut (v,
      (if equiv_dec string_eqdec v oldvar
       then s_UU2081_
       else nnrs_stmt_rename_md fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_md fruntime s_UU2082_ oldvar newvar))
  | NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMutColl (v,
      (nnrs_stmt_rename_md fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_md fruntime s_UU2082_ oldvar newvar))
  | NNRSAssign (v, e) ->
    NNRSAssign ((if equiv_dec string_eqdec v oldvar then newvar else v), e)
  | NNRSPush (v, e) -> NNRSPush (v, e)
  | NNRSFor (v, e, s_UU2080_) ->
    NNRSFor (v, e, (nnrs_stmt_rename_md fruntime s_UU2080_ oldvar newvar))
  | NNRSIf (e, s_UU2081_, s_UU2082_) ->
    NNRSIf (e, (nnrs_stmt_rename_md fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_md fruntime s_UU2082_ oldvar newvar))
  | NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
    NNRSEither (e, x_UU2081_,
      (nnrs_stmt_rename_md fruntime s_UU2081_ oldvar newvar), x_UU2082_,
      (nnrs_stmt_rename_md fruntime s_UU2082_ oldvar newvar))

(** val nnrs_expr_rename_env :
    foreign_runtime -> nnrs_expr -> var -> var -> nnrs_expr **)

let rec nnrs_expr_rename_env fruntime e oldvar newvar =
  match e with
  | NNRSVar v ->
    NNRSVar (if equiv_dec string_eqdec v oldvar then newvar else v)
  | NNRSBinop (b, e_UU2081_, e_UU2082_) ->
    NNRSBinop (b, (nnrs_expr_rename_env fruntime e_UU2081_ oldvar newvar),
      (nnrs_expr_rename_env fruntime e_UU2082_ oldvar newvar))
  | NNRSUnop (u, e_UU2080_) ->
    NNRSUnop (u, (nnrs_expr_rename_env fruntime e_UU2080_ oldvar newvar))
  | NNRSGroupBy (g, ls, e_UU2080_) ->
    NNRSGroupBy (g, ls,
      (nnrs_expr_rename_env fruntime e_UU2080_ oldvar newvar))
  | x -> x

(** val nnrs_stmt_rename_env :
    foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt **)

let rec nnrs_stmt_rename_env fruntime s oldvar newvar =
  match s with
  | NNRSSeq (s_UU2081_, s_UU2082_) ->
    NNRSSeq ((nnrs_stmt_rename_env fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_env fruntime s_UU2082_ oldvar newvar))
  | NNRSLet (v, e, s_UU2080_) ->
    NNRSLet (v, (nnrs_expr_rename_env fruntime e oldvar newvar),
      (if equiv_dec string_eqdec v oldvar
       then s_UU2080_
       else nnrs_stmt_rename_env fruntime s_UU2080_ oldvar newvar))
  | NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMut (v, (nnrs_stmt_rename_env fruntime s_UU2081_ oldvar newvar),
      (if equiv_dec string_eqdec v oldvar
       then s_UU2082_
       else nnrs_stmt_rename_env fruntime s_UU2082_ oldvar newvar))
  | NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
    NNRSLetMutColl (v,
      (nnrs_stmt_rename_env fruntime s_UU2081_ oldvar newvar),
      (if equiv_dec string_eqdec v oldvar
       then s_UU2082_
       else nnrs_stmt_rename_env fruntime s_UU2082_ oldvar newvar))
  | NNRSAssign (v, e) ->
    NNRSAssign (v, (nnrs_expr_rename_env fruntime e oldvar newvar))
  | NNRSPush (v, e) ->
    NNRSPush (v, (nnrs_expr_rename_env fruntime e oldvar newvar))
  | NNRSFor (v, e, s_UU2080_) ->
    NNRSFor (v, (nnrs_expr_rename_env fruntime e oldvar newvar),
      (if equiv_dec string_eqdec v oldvar
       then s_UU2080_
       else nnrs_stmt_rename_env fruntime s_UU2080_ oldvar newvar))
  | NNRSIf (e, s_UU2081_, s_UU2082_) ->
    NNRSIf ((nnrs_expr_rename_env fruntime e oldvar newvar),
      (nnrs_stmt_rename_env fruntime s_UU2081_ oldvar newvar),
      (nnrs_stmt_rename_env fruntime s_UU2082_ oldvar newvar))
  | NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
    NNRSEither ((nnrs_expr_rename_env fruntime e oldvar newvar), x_UU2081_,
      (if equiv_dec string_eqdec x_UU2081_ oldvar
       then s_UU2081_
       else nnrs_stmt_rename_env fruntime s_UU2081_ oldvar newvar),
      x_UU2082_,
      (if equiv_dec string_eqdec x_UU2082_ oldvar
       then s_UU2082_
       else nnrs_stmt_rename_env fruntime s_UU2082_ oldvar newvar))
