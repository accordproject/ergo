open Assoc
open Datatypes
open ForeignRuntime
open Fresh
open List0
open NNRC
open Var
open CNNRC
open CNNRCVars

type nnrcKind =
| Coq_nnrcExpr
| Coq_nnrcStmt

type nnrc_with_substs = NNRC.nnrc * (var * NNRC.nnrc) list

(** val mk_expr_from_vars :
    foreign_runtime -> nnrc_with_substs -> NNRC.nnrc **)

let mk_expr_from_vars _ nws =
  fold_right (fun sdef accum -> NNRCLet ((fst sdef), (snd sdef), accum))
    (fst nws) (snd nws)

(** val stratify1_aux :
    foreign_runtime -> NNRC.nnrc -> nnrcKind -> var list -> (var * NNRC.nnrc)
    list -> nnrc_with_substs **)

let stratify1_aux _ body required_kind bound_vars sdefs =
  match required_kind with
  | Coq_nnrcExpr ->
    let fvar =
      fresh_var ('s'::('t'::('r'::('a'::('t'::('i'::('f'::('y'::[]))))))))
        bound_vars
    in
    ((NNRCVar fvar), (app sdefs ((fvar, body) :: [])))
  | Coq_nnrcStmt -> (body, sdefs)

(** val stratify_aux :
    foreign_runtime -> NNRC.nnrc -> nnrcKind -> var list -> nnrc_with_substs **)

let rec stratify_aux fruntime e required_kind bound_vars =
  match e with
  | NNRCBinop (b, e1, e2) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    let bound_vars2 = app (domain sdefs1) bound_vars in
    let (e2', sdefs2) = stratify_aux fruntime e2 Coq_nnrcExpr bound_vars2 in
    ((NNRCBinop (b, e1', e2')), (app sdefs1 sdefs2))
  | NNRCUnop (u, e1) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    ((NNRCUnop (u, e1')), sdefs1)
  | NNRCLet (x, e1, e2) ->
    let e1'ws = stratify_aux fruntime e1 Coq_nnrcStmt bound_vars in
    let e1' = mk_expr_from_vars fruntime e1'ws in
    let e2'ws = stratify_aux fruntime e2 Coq_nnrcStmt (x :: bound_vars) in
    let e2' = mk_expr_from_vars fruntime e2'ws in
    stratify1_aux fruntime (NNRCLet (x, e1', e2')) required_kind bound_vars []
  | NNRCFor (x, e1, e2) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    let bound_vars2 = app (domain sdefs1) (x :: bound_vars) in
    let e2'ws = stratify_aux fruntime e2 Coq_nnrcStmt (x :: bound_vars) in
    let e2' = mk_expr_from_vars fruntime e2'ws in
    stratify1_aux fruntime (NNRCFor (x, e1', e2')) required_kind bound_vars2
      sdefs1
  | NNRCIf (e1, e2, e3) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    let bound_vars2 = app (domain sdefs1) bound_vars in
    let e2'ws = stratify_aux fruntime e2 Coq_nnrcStmt bound_vars in
    let e2' = mk_expr_from_vars fruntime e2'ws in
    let e3'ws = stratify_aux fruntime e3 Coq_nnrcStmt bound_vars in
    let e3' = mk_expr_from_vars fruntime e3'ws in
    stratify1_aux fruntime (NNRCIf (e1', e2', e3')) required_kind bound_vars2
      sdefs1
  | NNRCEither (e1, x2, e2, x3, e3) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    let bound_vars2 = app (domain sdefs1) bound_vars in
    let e2'ws = stratify_aux fruntime e2 Coq_nnrcStmt (x2 :: bound_vars) in
    let e2' = mk_expr_from_vars fruntime e2'ws in
    let e3'ws = stratify_aux fruntime e3 Coq_nnrcStmt (x3 :: bound_vars) in
    let e3' = mk_expr_from_vars fruntime e3'ws in
    stratify1_aux fruntime (NNRCEither (e1', x2, e2', x3, e3')) required_kind
      (x2 :: (x3 :: bound_vars2)) sdefs1
  | NNRCGroupBy (s, ls, e1) ->
    let (e1', sdefs1) = stratify_aux fruntime e1 Coq_nnrcExpr bound_vars in
    stratify1_aux fruntime (NNRCGroupBy (s, ls, e1')) required_kind
      bound_vars sdefs1
  | _ -> (e, [])

(** val stratify : foreign_runtime -> NNRC.nnrc -> NNRC.nnrc **)

let stratify fruntime e =
  mk_expr_from_vars fruntime
    (stratify_aux fruntime e Coq_nnrcStmt (nnrc_free_vars fruntime e))
