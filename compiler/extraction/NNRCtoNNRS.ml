open Datatypes
open ForeignRuntime
open Fresh
open Lift
open NNRC
open NNRCStratify
open NNRS
open Var
open CNNRC
open CNNRCVars

(** val nnrc_expr_to_nnrs_expr :
    foreign_runtime -> NNRC.nnrc -> nnrs_expr option **)

let rec nnrc_expr_to_nnrs_expr fruntime = function
| NNRCGetConstant c -> Some (NNRSGetConstant c)
| NNRCVar x -> Some (NNRSVar x)
| NNRCConst d -> Some (NNRSConst d)
| NNRCBinop (b, e1, e2) ->
  lift2 (fun x x0 -> NNRSBinop (b, x, x0))
    (nnrc_expr_to_nnrs_expr fruntime e1) (nnrc_expr_to_nnrs_expr fruntime e2)
| NNRCUnop (u, e1) ->
  lift (fun x -> NNRSUnop (u, x)) (nnrc_expr_to_nnrs_expr fruntime e1)
| NNRCGroupBy (s, ls, e1) ->
  lift (fun x -> NNRSGroupBy (s, ls, x)) (nnrc_expr_to_nnrs_expr fruntime e1)
| _ -> None

(** val nnrc_expr_to_nnrs_expr_stratified_some :
    foreign_runtime -> NNRC.nnrc -> nnrs_expr **)

let rec nnrc_expr_to_nnrs_expr_stratified_some fruntime = function
| NNRCGetConstant v -> NNRSGetConstant v
| NNRCVar v -> NNRSVar v
| NNRCConst d -> NNRSConst d
| NNRCBinop (b, n, n0) ->
  let h = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  let h2 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n0 in
  NNRSBinop (b, h, h2)
| NNRCUnop (u, n) ->
  let h0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  NNRSUnop (u, h0)
| _ -> assert false (* absurd case *)

type terminator =
| Term_assign of var
| Term_push of var

(** val terminate :
    foreign_runtime -> terminator -> nnrs_expr -> nnrs_stmt **)

let terminate _ terminator0 e =
  match terminator0 with
  | Term_assign result -> NNRSAssign (result, e)
  | Term_push result -> NNRSPush (result, e)

(** val nnrc_stmt_to_nnrs_stmt_aux :
    foreign_runtime -> var list -> terminator -> NNRC.nnrc -> nnrs_stmt option **)

let rec nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 stmt = match stmt with
| NNRCLet (v, s1, s2) ->
  (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs (Term_assign v) s1 with
   | Some s1' ->
     (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 s2 with
      | Some s2' -> Some (NNRSLetMut (v, s1', s2'))
      | None -> None)
   | None -> None)
| NNRCFor (v, e, s) ->
  let tmp = fresh_var ('t'::('m'::('p'::[]))) fvs in
  (match nnrc_expr_to_nnrs_expr fruntime e with
   | Some e' ->
     (match nnrc_stmt_to_nnrs_stmt_aux fruntime (tmp :: fvs) (Term_push tmp) s with
      | Some s' ->
        Some (NNRSLetMutColl (tmp, (NNRSFor (v, e', s')),
          (terminate fruntime terminator0 (NNRSVar tmp))))
      | None -> None)
   | None -> None)
| NNRCIf (e, s1, s2) ->
  (match nnrc_expr_to_nnrs_expr fruntime e with
   | Some e' ->
     (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 s1 with
      | Some s1' ->
        (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 s2 with
         | Some s2' -> Some (NNRSIf (e', s1', s2'))
         | None -> None)
      | None -> None)
   | None -> None)
| NNRCEither (e, x1, s1, x2, s2) ->
  (match nnrc_expr_to_nnrs_expr fruntime e with
   | Some e' ->
     (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 s1 with
      | Some s1' ->
        (match nnrc_stmt_to_nnrs_stmt_aux fruntime fvs terminator0 s2 with
         | Some s2' -> Some (NNRSEither (e', x1, s1', x2, s2'))
         | None -> None)
      | None -> None)
   | None -> None)
| _ ->
  (match nnrc_expr_to_nnrs_expr fruntime stmt with
   | Some e -> Some (terminate fruntime terminator0 e)
   | None -> None)

(** val nnrc_stmt_to_nnrs :
    foreign_runtime -> var list -> NNRC.nnrc -> (nnrs_stmt * var) option **)

let nnrc_stmt_to_nnrs fruntime globals stmt =
  let fvs = app globals (nnrc_bound_vars fruntime stmt) in
  let ret = fresh_var ('r'::('e'::('t'::[]))) fvs in
  (match nnrc_stmt_to_nnrs_stmt_aux fruntime (ret :: fvs) (Term_assign ret)
           stmt with
   | Some stmt0 -> Some (stmt0, ret)
   | None -> None)

(** val nnrc_stmt_to_nnrs_stmt_aux_stratified_some :
    foreign_runtime -> var list -> terminator -> NNRC.nnrc -> nnrs_stmt **)

let rec nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term = function
| NNRCGetConstant v -> terminate fruntime term (NNRSGetConstant v)
| NNRCVar v -> terminate fruntime term (NNRSVar v)
| NNRCConst d -> terminate fruntime term (NNRSConst d)
| NNRCBinop (b, n, n0) ->
  let s0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  let s1 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n0 in
  terminate fruntime term (NNRSBinop (b, s0, s1))
| NNRCUnop (u, n) ->
  let s0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  terminate fruntime term (NNRSUnop (u, s0))
| NNRCLet (v, n, n0) ->
  let s0 =
    nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs (Term_assign v) n
  in
  let s1 = nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term n0 in
  NNRSLetMut (v, s0, s1)
| NNRCFor (v, n, n0) ->
  let s0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  let s1 =
    nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime
      ((fresh_var ('t'::('m'::('p'::[]))) fvs) :: fvs) (Term_push
      (fresh_var ('t'::('m'::('p'::[]))) fvs)) n0
  in
  NNRSLetMutColl ((fresh_var ('t'::('m'::('p'::[]))) fvs), (NNRSFor (v, s0,
  s1)),
  (terminate fruntime term (NNRSVar (fresh_var ('t'::('m'::('p'::[]))) fvs))))
| NNRCIf (n, n0, n1) ->
  let s0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  let s1 = nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term n0 in
  let s2 = nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term n1 in
  NNRSIf (s0, s1, s2)
| NNRCEither (n, v, n0, v0, n1) ->
  let s0 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  let s1 = nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term n0 in
  let s2 = nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime fvs term n1 in
  NNRSEither (s0, v, s1, v0, s2)
| NNRCGroupBy (s0, l, n) ->
  let s1 = nnrc_expr_to_nnrs_expr_stratified_some fruntime n in
  terminate fruntime term (NNRSGroupBy (s0, l, s1))

(** val nnrc_stmt_to_nnrs_stmt_stratified_some :
    foreign_runtime -> var list -> NNRC.nnrc -> (nnrs_stmt * var) **)

let nnrc_stmt_to_nnrs_stmt_stratified_some fruntime fvs s =
  match nnrc_stmt_to_nnrs fruntime fvs s with
  | Some p -> p
  | None ->
    let s0 =
      nnrc_stmt_to_nnrs_stmt_aux_stratified_some fruntime
        ((fresh_var ('r'::('e'::('t'::[])))
           (app fvs (nnrc_bound_vars fruntime s))) :: (app fvs
                                                        (nnrc_bound_vars
                                                          fruntime s)))
        (Term_assign
        (fresh_var ('r'::('e'::('t'::[])))
          (app fvs (nnrc_bound_vars fruntime s)))) s
    in
    (s0,
    (fresh_var ('r'::('e'::('t'::[]))) (app fvs (nnrc_bound_vars fruntime s))))

(** val stratified_nnrc_stmt_to_nnrs :
    foreign_runtime -> var list -> NNRC.nnrc -> nnrs **)

let stratified_nnrc_stmt_to_nnrs =
  nnrc_stmt_to_nnrs_stmt_stratified_some

(** val nnrc_to_nnrs_top :
    foreign_runtime -> var list -> NNRC.nnrc -> nnrs **)

let nnrc_to_nnrs_top fruntime globals q =
  let nnrc_stratified = stratify fruntime q in
  stratified_nnrc_stmt_to_nnrs fruntime globals nnrc_stratified
