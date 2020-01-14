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

val mk_expr_from_vars : foreign_runtime -> nnrc_with_substs -> NNRC.nnrc

val stratify1_aux :
  foreign_runtime -> NNRC.nnrc -> nnrcKind -> var list -> (var * NNRC.nnrc)
  list -> nnrc_with_substs

val stratify_aux :
  foreign_runtime -> NNRC.nnrc -> nnrcKind -> var list -> nnrc_with_substs

val stratify : foreign_runtime -> NNRC.nnrc -> NNRC.nnrc
