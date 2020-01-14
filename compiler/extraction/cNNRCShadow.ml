open Bag
open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open List0
open String0
open UnaryOperators
open Var
open CNNRC
open CNNRCVars

(** val pick_new_really_fresh_in :
    foreign_runtime -> char list -> var -> var list -> nnrc -> char list **)

let pick_new_really_fresh_in fruntime sep name avoid e =
  if in_dec string_eqdec name
       (app avoid
         (app (nnrc_free_vars fruntime e) (nnrc_bound_vars fruntime e)))
  then really_fresh_in fruntime sep name avoid e
  else name

(** val pick_same_really_fresh_in :
    foreign_runtime -> char list -> var -> var list -> nnrc -> char list **)

let pick_same_really_fresh_in fruntime sep name avoid e =
  if in_dec string_eqdec name (app avoid (nnrc_bound_vars fruntime e))
  then really_fresh_in fruntime sep name avoid e
  else name

(** val nnrc_rename_lazy : foreign_runtime -> nnrc -> var -> var -> nnrc **)

let nnrc_rename_lazy fruntime e oldvar newvar =
  if equiv_dec string_eqdec oldvar newvar
  then e
  else nnrc_subst fruntime e oldvar (NNRCVar newvar)

(** val nnrc_pick_name :
    foreign_runtime -> char list -> (char list -> char list) -> var list ->
    var -> nnrc -> char list **)

let nnrc_pick_name fruntime sep renamer avoid oldvar e =
  let name = renamer oldvar in
  if equiv_dec string_eqdec name oldvar
  then pick_same_really_fresh_in fruntime sep name avoid e
  else pick_new_really_fresh_in fruntime sep name avoid e

(** val unshadow :
    foreign_runtime -> char list -> (char list -> char list) -> var list ->
    nnrc -> nnrc **)

let rec unshadow fruntime sep renamer avoid = function
| NNRCBinop (bop, e1, e2) ->
  NNRCBinop (bop, (unshadow fruntime sep renamer avoid e1),
    (unshadow fruntime sep renamer avoid e2))
| NNRCUnop (uop, e1) ->
  NNRCUnop (uop, (unshadow fruntime sep renamer avoid e1))
| NNRCLet (x, e1, e2) ->
  let e1' = unshadow fruntime sep renamer avoid e1 in
  let e2' = unshadow fruntime sep renamer avoid e2 in
  let x' = nnrc_pick_name fruntime sep renamer avoid x e2' in
  NNRCLet (x', e1', (nnrc_rename_lazy fruntime e2' x x'))
| NNRCFor (x, e1, e2) ->
  let e1' = unshadow fruntime sep renamer avoid e1 in
  let e2' = unshadow fruntime sep renamer avoid e2 in
  let x' = nnrc_pick_name fruntime sep renamer avoid x e2' in
  NNRCFor (x', e1', (nnrc_rename_lazy fruntime e2' x x'))
| NNRCIf (e1, e2, e3) ->
  NNRCIf ((unshadow fruntime sep renamer avoid e1),
    (unshadow fruntime sep renamer avoid e2),
    (unshadow fruntime sep renamer avoid e3))
| NNRCEither (ed, xl, el, xr, er) ->
  let ed' = unshadow fruntime sep renamer avoid ed in
  let el' = unshadow fruntime sep renamer avoid el in
  let er' = unshadow fruntime sep renamer avoid er in
  let xl' = nnrc_pick_name fruntime sep renamer avoid xl el' in
  let xr' = nnrc_pick_name fruntime sep renamer avoid xr er' in
  NNRCEither (ed', xl', (nnrc_rename_lazy fruntime el' xl xl'), xr',
  (nnrc_rename_lazy fruntime er' xr xr'))
| NNRCGroupBy (g, sl, e1) ->
  NNRCGroupBy (g, sl, (unshadow fruntime sep renamer avoid e1))
| x -> x

(** val nnrc_subst_const_to_var :
    foreign_runtime -> char list list -> nnrc -> nnrc **)

let rec nnrc_subst_const_to_var fruntime constants = function
| NNRCGetConstant y ->
  if in_dec string_eqdec y constants then NNRCVar y else NNRCGetConstant y
| NNRCBinop (bop, e1, e2) ->
  NNRCBinop (bop, (nnrc_subst_const_to_var fruntime constants e1),
    (nnrc_subst_const_to_var fruntime constants e2))
| NNRCUnop (uop, e1) ->
  NNRCUnop (uop, (nnrc_subst_const_to_var fruntime constants e1))
| NNRCLet (y, e1, e2) ->
  NNRCLet (y, (nnrc_subst_const_to_var fruntime constants e1),
    (nnrc_subst_const_to_var fruntime constants e2))
| NNRCFor (y, e1, e2) ->
  NNRCFor (y, (nnrc_subst_const_to_var fruntime constants e1),
    (nnrc_subst_const_to_var fruntime constants e2))
| NNRCIf (e1, e2, e3) ->
  NNRCIf ((nnrc_subst_const_to_var fruntime constants e1),
    (nnrc_subst_const_to_var fruntime constants e2),
    (nnrc_subst_const_to_var fruntime constants e3))
| NNRCEither (ed, xl, el, xr, er) ->
  NNRCEither ((nnrc_subst_const_to_var fruntime constants ed), xl,
    (nnrc_subst_const_to_var fruntime constants el), xr,
    (nnrc_subst_const_to_var fruntime constants er))
| NNRCGroupBy (g, sl, e1) ->
  NNRCGroupBy (g, sl, (nnrc_subst_const_to_var fruntime constants e1))
| x -> x

(** val closeFreeVars :
    foreign_runtime -> char list -> (char list -> char list) -> nnrc -> nnrc
    -> char list list -> nnrc **)

let closeFreeVars fruntime safeSeparator identifierSanitize input_e e _ =
  let all_free_vars = bdistinct string_eqdec (nnrc_global_vars fruntime e) in
  let unshadowed_e =
    unshadow fruntime safeSeparator identifierSanitize all_free_vars e
  in
  let unconsted_e =
    nnrc_subst_const_to_var fruntime all_free_vars unshadowed_e
  in
  let wrap_one_free_var = fun e' fv ->
    if in_dec string_dec fv all_free_vars
    then NNRCLet (fv, (NNRCUnop ((OpDot fv), input_e)), e')
    else e'
  in
  fold_left wrap_one_free_var all_free_vars unconsted_e
