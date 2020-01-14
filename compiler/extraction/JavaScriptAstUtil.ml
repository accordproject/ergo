open JsSyntax

(** val array_push : expr -> expr -> expr **)

let array_push e1 e2 =
  Coq_expr_call ((Coq_expr_member (e1, ('p'::('u'::('s'::('h'::[])))))),
    (e2 :: []))

(** val array_get : expr -> expr -> expr **)

let array_get e1 e2 =
  Coq_expr_access (e1, e2)

(** val object_hasOwnProperty : expr -> expr -> expr **)

let object_hasOwnProperty e1 e2 =
  Coq_expr_call ((Coq_expr_member (e1,
    ('h'::('a'::('s'::('O'::('w'::('n'::('P'::('r'::('o'::('p'::('e'::('r'::('t'::('y'::[])))))))))))))))),
    (e2 :: []))

(** val call_js_function : char list -> expr list -> expr **)

let call_js_function f args =
  Coq_expr_call ((Coq_expr_identifier f), args)

(** val call_runtime : char list -> expr list -> expr **)

let call_runtime =
  call_js_function
