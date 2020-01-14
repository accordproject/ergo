open Datatypes
open ForeignRuntime
open Fresh
open Imp
open ImpData
open Lift
open NNRSimp
open NNRSimpVars
open UnaryOperators

(** val nnrs_imp_expr_to_imp_data :
    foreign_runtime -> char list -> nnrs_imp_expr -> imp_data_expr **)

let rec nnrs_imp_expr_to_imp_data fruntime constants = function
| NNRSimpGetConstant x ->
  ImpExprOp ((DataOpUnary (OpDot x)), ((ImpExprVar constants) :: []))
| NNRSimpVar x -> ImpExprVar x
| NNRSimpConst d -> ImpExprConst d
| NNRSimpBinop (op, e1, e2) ->
  let e1' = nnrs_imp_expr_to_imp_data fruntime constants e1 in
  let e2' = nnrs_imp_expr_to_imp_data fruntime constants e2 in
  ImpExprOp ((DataOpBinary op), (e1' :: (e2' :: [])))
| NNRSimpUnop (op, e) ->
  let e' = nnrs_imp_expr_to_imp_data fruntime constants e in
  ImpExprOp ((DataOpUnary op), (e' :: []))
| NNRSimpGroupBy (g, fields, e) ->
  let e' = nnrs_imp_expr_to_imp_data fruntime constants e in
  ImpExprRuntimeCall ((DataRuntimeGroupby (g, fields)), (e' :: []))

(** val nnrs_imp_stmt_to_imp_data :
    foreign_runtime -> char list -> nnrs_imp_stmt -> imp_data_stmt **)

let rec nnrs_imp_stmt_to_imp_data fruntime constants = function
| NNRSimpSkip -> ImpStmtBlock ([], [])
| NNRSimpSeq (s1, s2) ->
  ImpStmtBlock ([],
    ((nnrs_imp_stmt_to_imp_data fruntime constants s1) :: ((nnrs_imp_stmt_to_imp_data
                                                             fruntime
                                                             constants s2) :: [])))
| NNRSimpAssign (x, e) ->
  ImpStmtAssign (x, (nnrs_imp_expr_to_imp_data fruntime constants e))
| NNRSimpLet (x, e, s) ->
  ImpStmtBlock (((x,
    (lift (nnrs_imp_expr_to_imp_data fruntime constants) e)) :: []),
    ((nnrs_imp_stmt_to_imp_data fruntime constants s) :: []))
| NNRSimpFor (x, e, s) ->
  ImpStmtFor (x, (nnrs_imp_expr_to_imp_data fruntime constants e),
    (nnrs_imp_stmt_to_imp_data fruntime constants s))
| NNRSimpIf (e, s1, s2) ->
  ImpStmtIf ((nnrs_imp_expr_to_imp_data fruntime constants e),
    (nnrs_imp_stmt_to_imp_data fruntime constants s1),
    (nnrs_imp_stmt_to_imp_data fruntime constants s2))
| NNRSimpEither (e, x1, s1, x2, s2) ->
  let e' = nnrs_imp_expr_to_imp_data fruntime constants e in
  ImpStmtIf ((ImpExprRuntimeCall (DataRuntimeEither, (e' :: []))),
  (ImpStmtBlock (((x1, (Some (ImpExprRuntimeCall (DataRuntimeToLeft,
  (e' :: []))))) :: []),
  ((nnrs_imp_stmt_to_imp_data fruntime constants s1) :: []))), (ImpStmtBlock
  (((x2, (Some (ImpExprRuntimeCall (DataRuntimeToRight,
  (e' :: []))))) :: []),
  ((nnrs_imp_stmt_to_imp_data fruntime constants s2) :: []))))

(** val nnrs_imp_to_imp_data_function :
    foreign_runtime -> nnrs_imp -> (imp_data_constant, imp_data_op,
    imp_data_runtime_op) imp_function **)

let nnrs_imp_to_imp_data_function fruntime = function
| (stmt, ret) ->
  let constants =
    let fv = nnrs_imp_stmt_free_vars fruntime stmt in
    let bv = nnrs_imp_stmt_bound_vars fruntime stmt in
    fresh_var
      ('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::('s'::[])))))))))
      (ret :: (app fv bv))
  in
  let body = nnrs_imp_stmt_to_imp_data fruntime constants stmt in
  ImpFun (constants, body, ret)

(** val nnrs_imp_to_imp_data_top :
    foreign_runtime -> char list -> nnrs_imp -> (imp_data_constant,
    imp_data_op, imp_data_runtime_op) imp **)

let nnrs_imp_to_imp_data_top fruntime qname q =
  (qname, (nnrs_imp_to_imp_data_function fruntime q)) :: []
