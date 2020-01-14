open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open Fresh
open List0
open Var
open CNNRC

(** val nnrc_global_vars : foreign_runtime -> nnrc -> var list **)

let rec nnrc_global_vars fruntime = function
| NNRCGetConstant x -> x :: []
| NNRCBinop (_, e1, e2) ->
  app (nnrc_global_vars fruntime e1) (nnrc_global_vars fruntime e2)
| NNRCUnop (_, e1) -> nnrc_global_vars fruntime e1
| NNRCLet (x, e1, e2) ->
  app (nnrc_global_vars fruntime e1)
    (remove string_eqdec x (nnrc_global_vars fruntime e2))
| NNRCFor (x, e1, e2) ->
  app (nnrc_global_vars fruntime e1)
    (remove string_eqdec x (nnrc_global_vars fruntime e2))
| NNRCIf (e1, e2, e3) ->
  app (nnrc_global_vars fruntime e1)
    (app (nnrc_global_vars fruntime e2) (nnrc_global_vars fruntime e3))
| NNRCEither (ed, xl, el, xr, er) ->
  app (nnrc_global_vars fruntime ed)
    (app (remove string_eqdec xl (nnrc_global_vars fruntime el))
      (remove string_eqdec xr (nnrc_global_vars fruntime er)))
| NNRCGroupBy (_, _, e0) -> nnrc_global_vars fruntime e0
| _ -> []

(** val nnrc_bound_vars : foreign_runtime -> nnrc -> var list **)

let rec nnrc_bound_vars fruntime = function
| NNRCBinop (_, e1, e2) ->
  app (nnrc_bound_vars fruntime e1) (nnrc_bound_vars fruntime e2)
| NNRCUnop (_, e1) -> nnrc_bound_vars fruntime e1
| NNRCLet (x, e1, e2) ->
  x :: (app (nnrc_bound_vars fruntime e1) (nnrc_bound_vars fruntime e2))
| NNRCFor (x, e1, e2) ->
  x :: (app (nnrc_bound_vars fruntime e1) (nnrc_bound_vars fruntime e2))
| NNRCIf (e1, e2, e3) ->
  app (nnrc_bound_vars fruntime e1)
    (app (nnrc_bound_vars fruntime e2) (nnrc_bound_vars fruntime e3))
| NNRCEither (ed, xl, el, xr, er) ->
  xl :: (xr :: (app (nnrc_bound_vars fruntime ed)
                 (app (nnrc_bound_vars fruntime el)
                   (nnrc_bound_vars fruntime er))))
| NNRCGroupBy (_, _, e0) -> nnrc_bound_vars fruntime e0
| _ -> []

(** val nnrc_free_vars : foreign_runtime -> nnrc -> var list **)

let rec nnrc_free_vars fruntime = function
| NNRCVar x -> x :: []
| NNRCBinop (_, e1, e2) ->
  app (nnrc_free_vars fruntime e1) (nnrc_free_vars fruntime e2)
| NNRCUnop (_, e1) -> nnrc_free_vars fruntime e1
| NNRCLet (x, e1, e2) ->
  app (nnrc_free_vars fruntime e1)
    (remove string_eqdec x (nnrc_free_vars fruntime e2))
| NNRCFor (x, e1, e2) ->
  app (nnrc_free_vars fruntime e1)
    (remove string_eqdec x (nnrc_free_vars fruntime e2))
| NNRCIf (e1, e2, e3) ->
  app (nnrc_free_vars fruntime e1)
    (app (nnrc_free_vars fruntime e2) (nnrc_free_vars fruntime e3))
| NNRCEither (ed, xl, el, xr, er) ->
  app (nnrc_free_vars fruntime ed)
    (app (remove string_eqdec xl (nnrc_free_vars fruntime el))
      (remove string_eqdec xr (nnrc_free_vars fruntime er)))
| NNRCGroupBy (_, _, e0) -> nnrc_free_vars fruntime e0
| _ -> []

(** val nnrc_subst : foreign_runtime -> nnrc -> var -> nnrc -> nnrc **)

let rec nnrc_subst fruntime e x e' =
  match e with
  | NNRCVar y -> if equiv_dec string_eqdec y x then e' else NNRCVar y
  | NNRCBinop (bop, e1, e2) ->
    NNRCBinop (bop, (nnrc_subst fruntime e1 x e'),
      (nnrc_subst fruntime e2 x e'))
  | NNRCUnop (uop, e1) -> NNRCUnop (uop, (nnrc_subst fruntime e1 x e'))
  | NNRCLet (y, e1, e2) ->
    NNRCLet (y, (nnrc_subst fruntime e1 x e'),
      (if equiv_dec string_eqdec y x then e2 else nnrc_subst fruntime e2 x e'))
  | NNRCFor (y, e1, e2) ->
    NNRCFor (y, (nnrc_subst fruntime e1 x e'),
      (if equiv_dec string_eqdec y x then e2 else nnrc_subst fruntime e2 x e'))
  | NNRCIf (e1, e2, e3) ->
    NNRCIf ((nnrc_subst fruntime e1 x e'), (nnrc_subst fruntime e2 x e'),
      (nnrc_subst fruntime e3 x e'))
  | NNRCEither (ed, xl, el, xr, er) ->
    NNRCEither ((nnrc_subst fruntime ed x e'), xl,
      (if equiv_dec string_eqdec xl x then el else nnrc_subst fruntime el x e'),
      xr,
      (if equiv_dec string_eqdec xr x then er else nnrc_subst fruntime er x e'))
  | NNRCGroupBy (g, sl, e1) ->
    NNRCGroupBy (g, sl, (nnrc_subst fruntime e1 x e'))
  | x0 -> x0

(** val really_fresh_in :
    foreign_runtime -> char list -> var -> var list -> nnrc -> char list **)

let really_fresh_in fruntime sep oldvar avoid e =
  fresh_var_from sep oldvar
    (app avoid (app (nnrc_free_vars fruntime e) (nnrc_bound_vars fruntime e)))
