
type var = char list

type ('constant, 'op, 'runtime) imp_expr =
| ImpExprError of char list
| ImpExprVar of var
| ImpExprConst of 'constant
| ImpExprOp of 'op * ('constant, 'op, 'runtime) imp_expr list
| ImpExprRuntimeCall of 'runtime * ('constant, 'op, 'runtime) imp_expr list

type ('constant, 'op, 'runtime) imp_stmt =
| ImpStmtBlock of (var * ('constant, 'op, 'runtime) imp_expr option) list
   * ('constant, 'op, 'runtime) imp_stmt list
| ImpStmtAssign of var * ('constant, 'op, 'runtime) imp_expr
| ImpStmtFor of var * ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_stmt
| ImpStmtForRange of var * ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_expr * ('constant, 'op, 'runtime) imp_stmt
| ImpStmtIf of ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_stmt * ('constant, 'op, 'runtime) imp_stmt

type ('constant, 'op, 'runtime) imp_function =
| ImpFun of var * ('constant, 'op, 'runtime) imp_stmt * var

type ('constant, 'op, 'runtime) imp =
  (char list * ('constant, 'op, 'runtime) imp_function) list
  (* singleton inductive, whose constructor was ImpLib *)
