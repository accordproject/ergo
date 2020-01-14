open BinaryOperators
open Data
open Datatypes
open ForeignRuntime
open NNRS
open NNRSCrossShadow
open NNRSimp
open UnaryOperators

(** val nnrs_expr_to_nnrs_imp_expr :
    foreign_runtime -> nnrs_expr -> nnrs_imp_expr **)

let rec nnrs_expr_to_nnrs_imp_expr fruntime = function
| NNRSGetConstant v -> NNRSimpGetConstant v
| NNRSVar v -> NNRSimpVar v
| NNRSConst d -> NNRSimpConst d
| NNRSBinop (bop, e_UU2081_, e_UU2082_) ->
  NNRSimpBinop (bop, (nnrs_expr_to_nnrs_imp_expr fruntime e_UU2081_),
    (nnrs_expr_to_nnrs_imp_expr fruntime e_UU2082_))
| NNRSUnop (uop, e0) ->
  NNRSimpUnop (uop, (nnrs_expr_to_nnrs_imp_expr fruntime e0))
| NNRSGroupBy (g, sl, e0) ->
  NNRSimpGroupBy (g, sl, (nnrs_expr_to_nnrs_imp_expr fruntime e0))

(** val nnrs_stmt_to_nnrs_imp_stmt :
    foreign_runtime -> nnrs_stmt -> nnrs_imp_stmt **)

let rec nnrs_stmt_to_nnrs_imp_stmt fruntime = function
| NNRSSeq (s_UU2081_, s_UU2082_) ->
  NNRSimpSeq ((nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2081_),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2082_))
| NNRSLet (v, e, s_UU2080_) ->
  NNRSimpLet (v, (Some (nnrs_expr_to_nnrs_imp_expr fruntime e)),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2080_))
| NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
  NNRSimpLet (v, None, (NNRSimpSeq
    ((nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2081_),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2082_))))
| NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
  NNRSimpLet (v, (Some (NNRSimpUnop (OpDistinct, (NNRSimpConst (Coq_dcoll
    []))))), (NNRSimpSeq ((nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2081_),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2082_))))
| NNRSAssign (v, e) ->
  NNRSimpAssign (v, (nnrs_expr_to_nnrs_imp_expr fruntime e))
| NNRSPush (v, e) ->
  NNRSimpAssign (v, (NNRSimpBinop (OpBagUnion, (NNRSimpVar v), (NNRSimpUnop
    (OpBag, (nnrs_expr_to_nnrs_imp_expr fruntime e))))))
| NNRSFor (v, e, s_UU2080_) ->
  NNRSimpFor (v, (nnrs_expr_to_nnrs_imp_expr fruntime e),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2080_))
| NNRSIf (e, s_UU2081_, s_UU2082_) ->
  NNRSimpIf ((nnrs_expr_to_nnrs_imp_expr fruntime e),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2081_),
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2082_))
| NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
  NNRSimpEither ((nnrs_expr_to_nnrs_imp_expr fruntime e), x_UU2081_,
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2081_), x_UU2082_,
    (nnrs_stmt_to_nnrs_imp_stmt fruntime s_UU2082_))

(** val nnrs_to_nnrs_imp : foreign_runtime -> nnrs -> nnrs_imp **)

let nnrs_to_nnrs_imp fruntime s =
  ((nnrs_stmt_to_nnrs_imp_stmt fruntime (fst s)), (snd s))

(** val nnrs_to_nnrs_imp_top :
    foreign_runtime -> char list -> nnrs -> nnrs_imp **)

let nnrs_to_nnrs_imp_top fruntime sep s =
  nnrs_to_nnrs_imp fruntime (nnrs_uncross_shadow fruntime sep s)
