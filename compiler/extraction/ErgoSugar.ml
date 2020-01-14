open Ast
open Data
open Ergo
open Names

(** val coq_SReturnEmpty : 'a1 -> ('a1, 'a2) rergo_stmt **)

let coq_SReturnEmpty a =
  SReturn (a, (EConst (a, Coq_dunit)))

(** val coq_EFunReturnEmpty : 'a1 -> ('a1, 'a2) rergo_expr **)

let coq_EFunReturnEmpty a =
  EConst (a, Coq_dunit)

(** val coq_EOptionalDot :
    'a1 -> char list -> ('a1, 'a2) rergo_expr -> ('a1, 'a2, relative_name)
    ergo_expr **)

let coq_EOptionalDot a pname e =
  EMatch (a, e, (((CaseLetOption (a,
    ('$'::('o'::('p'::('t'::('i'::('o'::('n'::[]))))))), None)), (ESome (a,
    (EUnaryOperator (a, (EOpDot pname), (EVar (a, (None,
    ('$'::('o'::('p'::('t'::('i'::('o'::('n'::[]))))))))))))))) :: []),
    (ENone a))

(** val coq_EOptionalDefault :
    'a1 -> ('a1, 'a2) rergo_expr -> ('a1, 'a2) rergo_expr -> ('a1, 'a2,
    relative_name) ergo_expr **)

let coq_EOptionalDefault a e1 e2 =
  EMatch (a, e1, (((CaseLetOption (a,
    ('$'::('o'::('p'::('t'::('i'::('o'::('n'::[]))))))), None)), (EVar (a,
    (None, ('$'::('o'::('p'::('t'::('i'::('o'::('n'::[]))))))))))) :: []), e2)
