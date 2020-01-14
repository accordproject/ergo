open Datatypes
open EJson
open EJsonOperators
open EJsonRuntimeOperators
open ForeignEJson
open ForeignEJsonRuntime
open ForeignToJavaScriptAst
open Imp
open ImpEJson
open JavaScriptAst
open JavaScriptAstUtil
open JsSyntax
open List0
open ListAdd

(** val scope : stat list -> stat **)

let scope l =
  Coq_stat_block l

(** val prog_to_string : prog -> char list **)

let prog_to_string _ =
  []

(** val box_nat : expr -> expr **)

let box_nat e =
  Coq_expr_object (((Coq_propname_identifier ('$'::('n'::('a'::('t'::[]))))),
    (Coq_propbody_val e)) :: [])

(** val mk_expr_error : expr **)

let mk_expr_error =
  Coq_expr_literal Coq_literal_null

(** val mk_unary_expr : (expr -> expr) -> expr list -> expr **)

let mk_unary_expr f = function
| [] -> mk_expr_error
| e :: l -> (match l with
             | [] -> f e
             | _ :: _ -> mk_expr_error)

(** val mk_unary_op : unary_op -> expr list -> expr **)

let mk_unary_op op el =
  mk_unary_expr (fun x -> Coq_expr_unary_op (op, x)) el

(** val mk_binary_expr : (expr -> expr -> expr) -> expr list -> expr **)

let mk_binary_expr f = function
| [] -> mk_expr_error
| e1 :: l ->
  (match l with
   | [] -> mk_expr_error
   | e2 :: l0 -> (match l0 with
                  | [] -> f e1 e2
                  | _ :: _ -> mk_expr_error))

(** val mk_binary_op : binary_op -> expr list -> expr **)

let mk_binary_op op el =
  mk_binary_expr (fun e1 e2 -> Coq_expr_binary_op (e1, op, e2)) el

(** val mk_object : char list list -> expr list -> expr **)

let mk_object atts el =
  match zip atts el with
  | Some l ->
    Coq_expr_object
      (map (fun entry ->
        let (lbl, e) = entry in
        ((Coq_propname_identifier lbl), (Coq_propbody_val e))) l)
  | None -> mk_expr_error

(** val mk_runtime_call :
    'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> 'a2
    imp_ejson_runtime_op -> expr list -> expr **)

let mk_runtime_call fejson fejruntime op el =
  call_runtime (string_of_ejson_runtime_op fejson fejruntime op) el

(** val mk_integer_plus_one :
    'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> expr -> expr **)

let mk_integer_plus_one fejson fejruntime e =
  mk_runtime_call fejson fejruntime EJsonRuntimeNatPlus
    (e :: ((box_nat (Coq_expr_literal (Coq_literal_number
             ((fun x -> float_of_int x) 1)))) :: []))

(** val mk_integer_le :
    'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> expr -> expr ->
    expr **)

let mk_integer_le fejson fejruntime e1 e2 =
  mk_runtime_call fejson fejruntime EJsonRuntimeNatLe (e1 :: (e2 :: []))

(** val imp_ejson_op_to_js_ast : imp_ejson_op -> expr list -> expr **)

let imp_ejson_op_to_js_ast op el =
  match op with
  | EJsonOpNot -> mk_unary_op Coq_unary_op_not el
  | EJsonOpNeg -> mk_unary_op Coq_unary_op_neg el
  | EJsonOpAnd -> mk_binary_op Coq_binary_op_and el
  | EJsonOpOr -> mk_binary_op Coq_binary_op_or el
  | EJsonOpLt -> mk_binary_op Coq_binary_op_lt el
  | EJsonOpLe -> mk_binary_op Coq_binary_op_le el
  | EJsonOpGt -> mk_binary_op Coq_binary_op_gt el
  | EJsonOpGe -> mk_binary_op Coq_binary_op_ge el
  | EJsonOpSub -> mk_binary_op Coq_binary_op_sub el
  | EJsonOpMult -> mk_binary_op Coq_binary_op_mult el
  | EJsonOpDiv -> mk_binary_op Coq_binary_op_div el
  | EJsonOpStrictEqual -> mk_binary_op Coq_binary_op_strict_equal el
  | EJsonOpStrictDisequal -> mk_binary_op Coq_binary_op_strict_disequal el
  | EJsonOpArray -> Coq_expr_array (map (fun x -> Some x) el)
  | EJsonOpArrayLength ->
    mk_unary_expr (fun e -> Coq_expr_member (e,
      ('l'::('e'::('n'::('g'::('t'::('h'::[])))))))) el
  | EJsonOpArrayPush -> mk_binary_expr array_push el
  | EJsonOpArrayAccess -> mk_binary_expr array_get el
  | EJsonOpObject atts -> mk_object atts el
  | EJsonOpAccess att ->
    mk_binary_expr (fun x x0 -> Coq_expr_access (x, x0))
      (app el ((Coq_expr_literal (Coq_literal_string att)) :: []))
  | EJsonOpHasOwnProperty att ->
    mk_binary_expr object_hasOwnProperty
      (app el ((Coq_expr_literal (Coq_literal_string att)) :: []))
  | EJsonOpMathMin ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('m'::('i'::('n'::[]))))), el)
  | EJsonOpMathMax ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('m'::('a'::('x'::[]))))), el)
  | EJsonOpMathPow ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('p'::('o'::('w'::[]))))), el)
  | EJsonOpMathExp ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('e'::('x'::('p'::[]))))), el)
  | EJsonOpMathAbs ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('a'::('b'::('s'::[]))))), el)
  | EJsonOpMathLog ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('l'::('o'::('g'::('2'::[])))))), el)
  | EJsonOpMathLog10 ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))),
      ('l'::('o'::('g'::('1'::('0'::[]))))))), el)
  | EJsonOpMathSqrt ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('s'::('q'::('r'::('t'::[])))))), el)
  | EJsonOpMathCeil ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))), ('c'::('e'::('i'::('l'::[])))))), el)
  | EJsonOpMathFloor ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))),
      ('f'::('l'::('o'::('o'::('r'::[]))))))), el)
  | EJsonOpMathTrunc ->
    Coq_expr_call ((Coq_expr_member ((Coq_expr_identifier
      ('M'::('a'::('t'::('h'::[]))))),
      ('t'::('r'::('u'::('n'::('c'::[]))))))), el)
  | _ -> mk_binary_op Coq_binary_op_add el

(** val cejson_to_js_ast :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> 'a1 cejson ->
    expr **)

let cejson_to_js_ast fejson ftjast = function
| Coq_cejnull -> Coq_expr_literal Coq_literal_null
| Coq_cejnumber n -> Coq_expr_literal (Coq_literal_number n)
| Coq_cejbigint n ->
  box_nat (Coq_expr_literal (Coq_literal_number
    ((fun x -> float_of_int x) n)))
| Coq_cejbool b -> Coq_expr_literal (Coq_literal_bool b)
| Coq_cejstring s -> Coq_expr_literal (Coq_literal_string s)
| Coq_cejforeign fd -> foreign_ejson_to_ajavascript_expr fejson ftjast fd

(** val imp_ejson_expr_to_js_ast :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> ('a1, 'a2) imp_ejson_expr -> expr **)

let rec imp_ejson_expr_to_js_ast fejson ftjast fejruntime = function
| ImpExprError _ -> mk_expr_error
| ImpExprVar v -> Coq_expr_identifier v
| ImpExprConst j -> cejson_to_js_ast fejson ftjast j
| ImpExprOp (op, el) ->
  imp_ejson_op_to_js_ast op
    (map (imp_ejson_expr_to_js_ast fejson ftjast fejruntime) el)
| ImpExprRuntimeCall (rop, el) ->
  mk_runtime_call fejson fejruntime rop
    (map (imp_ejson_expr_to_js_ast fejson ftjast fejruntime) el)

(** val decl_to_js_ast :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> (var * ('a1 imp_ejson_constant, imp_ejson_op,
    'a2 imp_ejson_runtime_op) imp_expr option) -> var * expr option **)

let decl_to_js_ast fejson ftjast fejruntime = function
| (x, o) ->
  (match o with
   | Some e ->
     (x, (Some (imp_ejson_expr_to_js_ast fejson ftjast fejruntime e)))
   | None -> (x, None))

(** val imp_ejson_stmt_to_js_ast :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> ('a1, 'a2) imp_ejson_stmt -> stat **)

let rec imp_ejson_stmt_to_js_ast fejson ftjast fejruntime = function
| ImpStmtBlock (decls, stmts) ->
  scope ((Coq_stat_let_decl
    (map (decl_to_js_ast fejson ftjast fejruntime) decls)) :: (map
                                                                (imp_ejson_stmt_to_js_ast
                                                                  fejson
                                                                  ftjast
                                                                  fejruntime)
                                                                stmts))
| ImpStmtAssign (x, e) ->
  Coq_stat_expr (Coq_expr_assign ((Coq_expr_identifier x), None,
    (imp_ejson_expr_to_js_ast fejson ftjast fejruntime e)))
| ImpStmtFor (x, e, s) ->
  let c = imp_ejson_expr_to_js_ast fejson ftjast fejruntime e in
  let prog0 = Coq_prog_intro (strictness_true, ((Coq_element_stat
    (imp_ejson_stmt_to_js_ast fejson ftjast fejruntime s)) :: []))
  in
  let f = Coq_expr_function (None, (x :: []), (Coq_funcbody_intro (prog0,
    (prog_to_string prog0))))
  in
  Coq_stat_expr
  (call_runtime ('i'::('t'::('e'::('r'::('C'::('o'::('l'::('l'::[]))))))))
    (c :: (f :: [])))
| ImpStmtForRange (x, e1, e2, s) ->
  Coq_stat_for_let ([], ((x, (Some
    (imp_ejson_expr_to_js_ast fejson ftjast fejruntime e1))) :: []), (Some
    (mk_integer_le fejson fejruntime (Coq_expr_identifier x)
      (imp_ejson_expr_to_js_ast fejson ftjast fejruntime e2))), (Some
    (Coq_expr_assign ((Coq_expr_identifier x), None,
    (mk_integer_plus_one fejson fejruntime (Coq_expr_identifier x))))),
    (imp_ejson_stmt_to_js_ast fejson ftjast fejruntime s))
| ImpStmtIf (e, s1, s2) ->
  Coq_stat_if ((imp_ejson_expr_to_js_ast fejson ftjast fejruntime e),
    (imp_ejson_stmt_to_js_ast fejson ftjast fejruntime s1), (Some
    (imp_ejson_stmt_to_js_ast fejson ftjast fejruntime s2)))

(** val imp_ejson_function_to_js_ast :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
    imp_ejson_runtime_op) imp_function -> char list list * funcbody **)

let imp_ejson_function_to_js_ast fejson ftjast fejruntime = function
| ImpFun (v, s, ret) ->
  let body = imp_ejson_stmt_to_js_ast fejson ftjast fejruntime s in
  let ret0 =
    scope ((Coq_stat_let_decl ((ret,
      None) :: [])) :: (body :: ((Coq_stat_return (Some (Coq_expr_identifier
      ret))) :: [])))
  in
  let prog0 = Coq_prog_intro (strictness_true, ((Coq_element_stat
    ret0) :: []))
  in
  ((v :: []), (Coq_funcbody_intro (prog0, (prog_to_string prog0))))

(** val imp_ejson_function_to_funcelement :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
    imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> element **)

let imp_ejson_function_to_funcelement fejson ftjast fejruntime fname fbody =
  let (args, body) =
    imp_ejson_function_to_js_ast fejson ftjast fejruntime fbody
  in
  Coq_element_func_decl (fname, args, body)

(** val imp_ejson_function_to_funcdecl :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
    imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> funcdecl **)

let imp_ejson_function_to_funcdecl fejson ftjast fejruntime fname fbody =
  let (args, body) =
    imp_ejson_function_to_js_ast fejson ftjast fejruntime fbody
  in
  { funcdecl_name = fname; funcdecl_parameters = args; funcdecl_body = body }

(** val imp_ejson_function_to_topdecl :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
    imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> topdecl **)

let imp_ejson_function_to_topdecl fejson ftjast fejruntime fname fbody =
  Coq_elementdecl
    (imp_ejson_function_to_funcelement fejson ftjast fejruntime fname fbody)

(** val imp_ejson_to_function :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> ('a1, 'a2) imp_ejson -> topdecl list **)

let imp_ejson_to_function fejson ftjast fejruntime = function
| [] -> []
| p :: l0 ->
  let (fname, fbody) = p in
  (match l0 with
   | [] ->
     (imp_ejson_function_to_topdecl fejson ftjast fejruntime fname fbody) :: []
   | _ :: _ -> [])

(** val imp_ejson_to_method :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> ('a1, 'a2) imp_ejson -> funcdecl list **)

let imp_ejson_to_method fejson ftjast fejruntime = function
| [] -> []
| p :: l0 ->
  let (fname, fbody) = p in
  (match l0 with
   | [] ->
     (imp_ejson_function_to_funcdecl fejson ftjast fejruntime fname fbody) :: []
   | _ :: _ -> [])

(** val imp_ejson_table_to_topdecls :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> char list -> ('a1, 'a2) imp_ejson list ->
    topdecl list **)

let imp_ejson_table_to_topdecls fejson ftjast fejruntime cname q =
  (Coq_classdecl (cname,
    (concat (map (imp_ejson_to_method fejson ftjast fejruntime) q)))) :: []

(** val imp_ejson_table_to_class :
    'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
    foreign_ejson_runtime -> char list -> ('a1, 'a2) imp_ejson -> topdecl **)

let imp_ejson_table_to_class fejson ftjast fejruntime cname q =
  Coq_classdecl (cname,
    (map (fun xy ->
      imp_ejson_function_to_funcdecl fejson ftjast fejruntime (fst xy)
        (snd xy)) q))
