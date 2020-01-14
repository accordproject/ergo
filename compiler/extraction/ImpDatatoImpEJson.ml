open BinaryOperators
open BrandRelation
open DataNorm
open DataToEJson
open Datatypes
open EJson
open EJsonOperators
open EJsonRuntimeOperators
open Encode
open ForeignDataToEJson
open ForeignEJson
open ForeignEJsonRuntime
open ForeignRuntime
open ForeignToEJsonRuntime
open Imp
open ImpData
open ImpEJson
open Lift
open List0
open SortingDesc
open UnaryOperators

(** val mk_imp_ejson_expr_error : char list -> ('a1, 'a2) imp_ejson_expr **)

let mk_imp_ejson_expr_error msg =
  ImpExprError msg

(** val mk_imp_ejson_op :
    imp_ejson_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
    imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr **)

let mk_imp_ejson_op op el =
  ImpExprOp (op, el)

(** val mk_imp_ejson_runtime_call :
    'a2 imp_ejson_runtime_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
    imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr **)

let mk_imp_ejson_runtime_call op el =
  ImpExprRuntimeCall (op, el)

(** val mk_string : char list -> ('a1, 'a2) imp_ejson_expr **)

let mk_string s =
  ImpExprConst (Coq_cejstring s)

(** val mk_left :
    ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
    -> ('a1, 'a2) imp_ejson_expr **)

let mk_left e =
  mk_imp_ejson_op (EJsonOpObject
    (('$'::('l'::('e'::('f'::('t'::[]))))) :: [])) (e :: [])

(** val mk_right :
    ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
    -> ('a1, 'a2) imp_ejson_expr **)

let mk_right e =
  mk_imp_ejson_op (EJsonOpObject
    (('$'::('r'::('i'::('g'::('h'::('t'::[])))))) :: [])) (e :: [])

(** val mk_array :
    ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
    list -> ('a1, 'a2) imp_ejson_expr **)

let mk_array el =
  mk_imp_ejson_runtime_call EJsonRuntimeArray el

(** val mk_object :
    (char list * ('a1, 'a2) imp_ejson_expr) list -> ('a1, 'a2) imp_ejson_expr **)

let mk_object el =
  mk_imp_ejson_op (EJsonOpObject (map fst el)) (map snd el)

(** val mk_string_array : char list list -> ('a1, 'a2) imp_ejson_expr **)

let mk_string_array sl =
  mk_array (map (fun x -> ImpExprConst x) (map (fun x -> Coq_cejstring x) sl))

(** val ejson_to_expr : 'a1 ejson -> ('a1, 'a2) imp_ejson_expr **)

let rec ejson_to_expr = function
| Coq_ejnull -> ImpExprConst Coq_cejnull
| Coq_ejnumber f -> ImpExprConst (Coq_cejnumber f)
| Coq_ejbigint n -> ImpExprConst (Coq_cejbigint n)
| Coq_ejbool b -> ImpExprConst (Coq_cejbool b)
| Coq_ejstring s -> ImpExprConst (Coq_cejstring s)
| Coq_ejarray ls -> mk_array (map ejson_to_expr ls)
| Coq_ejobject ls ->
  mk_object (map (fun xy -> ((fst xy), (ejson_to_expr (snd xy)))) ls)
| Coq_ejforeign fd -> ImpExprConst (Coq_cejforeign fd)

(** val sortCriterias_to_ejson_expr :
    (char list * coq_SortDesc) list -> ('a1, 'a2) imp_ejson_expr **)

let sortCriterias_to_ejson_expr scl =
  mk_array (map ejson_to_expr (map sortCriteria_to_ejson scl))

(** val brands_to_ejson_expr : char list list -> ('a1, 'a2) imp_ejson_expr **)

let brands_to_ejson_expr =
  mk_string_array

(** val mk_either_expr :
    ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr **)

let mk_either_expr el =
  mk_imp_ejson_runtime_call EJsonRuntimeEither el

(** val mk_to_left_expr :
    ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr **)

let mk_to_left_expr el =
  mk_imp_ejson_runtime_call EJsonRuntimeToLeft el

(** val mk_to_right_expr :
    ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr **)

let mk_to_right_expr el =
  mk_imp_ejson_runtime_call EJsonRuntimeToRight el

(** val imp_data_unary_op_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> unary_op -> ('a1, 'a2) imp_ejson_expr list ->
    ('a1, 'a2) imp_ejson_expr **)

let imp_data_unary_op_to_imp_ejson _ _ _ _ fejtoruntime h op el = match el with
| [] ->
  mk_imp_ejson_expr_error
    ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[])))))))))))))))))))))))))
| e :: l ->
  (match l with
   | [] ->
     (match op with
      | OpIdentity -> e
      | OpNeg -> mk_imp_ejson_op EJsonOpNot (e :: [])
      | OpRec s ->
        mk_imp_ejson_op (EJsonOpObject ((key_encode s) :: [])) (e :: [])
      | OpDot s ->
        mk_imp_ejson_runtime_call EJsonRuntimeRecDot (e :: ((ImpExprConst
          (Coq_cejstring (key_encode s))) :: []))
      | OpRecRemove s ->
        mk_imp_ejson_runtime_call EJsonRuntimeRecRemove
          (e :: ((mk_string (key_encode s)) :: []))
      | OpRecProject fl ->
        mk_imp_ejson_runtime_call EJsonRuntimeRecProject
          (app (e :: []) ((mk_string_array (map key_encode fl)) :: []))
      | OpBag -> mk_array el
      | OpSingleton -> mk_imp_ejson_runtime_call EJsonRuntimeSingleton el
      | OpFlatten -> mk_imp_ejson_runtime_call EJsonRuntimeFlatten el
      | OpDistinct -> mk_imp_ejson_runtime_call EJsonRuntimeDistinct el
      | OpOrderBy scl ->
        mk_imp_ejson_runtime_call EJsonRuntimeSort
          ((sortCriterias_to_ejson_expr scl) :: (e :: []))
      | OpCount -> mk_imp_ejson_runtime_call EJsonRuntimeCount el
      | OpToString -> mk_imp_ejson_runtime_call EJsonRuntimeToString el
      | OpToText -> mk_imp_ejson_runtime_call EJsonRuntimeToText el
      | OpLength -> mk_imp_ejson_runtime_call EJsonRuntimeLength el
      | OpSubstring (start, len) ->
        let start0 = ImpExprConst (Coq_cejbigint start) in
        (match len with
         | Some len0 ->
           let args =
             let len1 = ImpExprConst (Coq_cejbigint len0) in
             e :: (start0 :: (len1 :: []))
           in
           mk_imp_ejson_runtime_call EJsonRuntimeSubstring args
         | None ->
           let args = e :: (start0 :: []) in
           mk_imp_ejson_runtime_call EJsonRuntimeSubstringEnd args)
      | OpLike pat ->
        mk_imp_ejson_runtime_call EJsonRuntimeLike ((ImpExprConst
          (Coq_cejstring pat)) :: (e :: []))
      | OpLeft -> mk_left e
      | OpRight -> mk_right e
      | OpBrand b ->
        mk_object ((('$'::('c'::('l'::('a'::('s'::('s'::[])))))),
          (brands_to_ejson_expr (canon_brands h b))) :: ((('$'::('d'::('a'::('t'::('a'::[]))))),
          e) :: []))
      | OpUnbrand -> mk_imp_ejson_runtime_call EJsonRuntimeUnbrand el
      | OpCast b ->
        mk_imp_ejson_runtime_call EJsonRuntimeCast
          ((brands_to_ejson_expr b) :: (e :: []))
      | OpNatUnary u ->
        let op0 =
          match u with
          | NatAbs -> EJsonRuntimeNatAbs
          | NatLog2 -> EJsonRuntimeNatLog2
          | NatSqrt -> EJsonRuntimeNatSqrt
        in
        mk_imp_ejson_runtime_call op0 (e :: [])
      | OpNatSum -> mk_imp_ejson_runtime_call EJsonRuntimeNatSum el
      | OpNatMin -> mk_imp_ejson_runtime_call EJsonRuntimeNatMin el
      | OpNatMax -> mk_imp_ejson_runtime_call EJsonRuntimeNatMax el
      | OpNatMean -> mk_imp_ejson_runtime_call EJsonRuntimeNatArithMean el
      | OpFloatOfNat -> mk_imp_ejson_runtime_call EJsonRuntimeFloatOfNat el
      | OpFloatUnary u ->
        let op0 =
          match u with
          | FloatNeg -> EJsonOpNeg
          | FloatSqrt -> EJsonOpMathSqrt
          | FloatExp -> EJsonOpMathExp
          | FloatLog -> EJsonOpMathLog
          | FloatLog10 -> EJsonOpMathLog10
          | FloatCeil -> EJsonOpMathCeil
          | FloatFloor -> EJsonOpMathFloor
          | FloatAbs -> EJsonOpMathAbs
        in
        mk_imp_ejson_op op0 (e :: [])
      | OpFloatTruncate ->
        mk_imp_ejson_runtime_call EJsonRuntimeNatOfFloat (e :: [])
      | OpFloatSum -> mk_imp_ejson_runtime_call EJsonRuntimeFloatSum el
      | OpFloatMean -> mk_imp_ejson_runtime_call EJsonRuntimeFloatArithMean el
      | OpFloatBagMin ->
        mk_imp_ejson_runtime_call EJsonRuntimeFloatMin (e :: [])
      | OpFloatBagMax ->
        mk_imp_ejson_runtime_call EJsonRuntimeFloatMax (e :: [])
      | OpForeignUnary fu ->
        mk_imp_ejson_runtime_call (EJsonRuntimeForeign
          (fejtoruntime.foreign_to_ejson_runtime_of_unary_op fu)) el)
   | _ :: _ ->
     mk_imp_ejson_expr_error
       ('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))

(** val imp_data_binary_op_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> binary_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
    imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr **)

let imp_data_binary_op_to_imp_ejson _ _ _ _ fejtoruntime op el = match el with
| [] ->
  mk_imp_ejson_expr_error
    ('i'::('m'::('p'::('_'::('d'::('a'::('t'::('a'::('_'::('b'::('i'::('n'::('a'::('r'::('y'::('_'::('o'::('p'::('_'::('t'::('o'::('_'::('i'::('m'::('p'::('_'::('e'::('j'::('s'::('o'::('n'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| e1 :: l ->
  (match l with
   | [] ->
     mk_imp_ejson_expr_error
       ('i'::('m'::('p'::('_'::('d'::('a'::('t'::('a'::('_'::('b'::('i'::('n'::('a'::('r'::('y'::('_'::('o'::('p'::('_'::('t'::('o'::('_'::('i'::('m'::('p'::('_'::('e'::('j'::('s'::('o'::('n'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | e2 :: l0 ->
     (match l0 with
      | [] ->
        (match op with
         | OpEqual -> mk_imp_ejson_runtime_call EJsonRuntimeEqual el
         | OpRecConcat -> mk_imp_ejson_runtime_call EJsonRuntimeRecConcat el
         | OpRecMerge -> mk_imp_ejson_runtime_call EJsonRuntimeRecMerge el
         | OpAnd -> mk_imp_ejson_op EJsonOpAnd el
         | OpOr -> mk_imp_ejson_op EJsonOpOr el
         | OpLt -> mk_imp_ejson_runtime_call EJsonRuntimeNatLt el
         | OpLe -> mk_imp_ejson_runtime_call EJsonRuntimeNatLe el
         | OpBagUnion ->
           mk_imp_ejson_runtime_call EJsonRuntimeUnion (e1 :: (e2 :: []))
         | OpBagDiff ->
           mk_imp_ejson_runtime_call EJsonRuntimeMinus (e1 :: (e2 :: []))
         | OpBagMin ->
           mk_imp_ejson_runtime_call EJsonRuntimeMin (e1 :: (e2 :: []))
         | OpBagMax ->
           mk_imp_ejson_runtime_call EJsonRuntimeMax (e1 :: (e2 :: []))
         | OpBagNth ->
           mk_imp_ejson_runtime_call EJsonRuntimeNth (e1 :: (e2 :: []))
         | OpContains ->
           mk_imp_ejson_runtime_call EJsonRuntimeContains (e1 :: (e2 :: []))
         | OpStringConcat -> mk_imp_ejson_op EJsonOpAddString el
         | OpStringJoin ->
           mk_imp_ejson_runtime_call EJsonRuntimeStringJoin (e1 :: (e2 :: []))
         | OpNatBinary opa ->
           (match opa with
            | NatPlus ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatPlus (e1 :: (e2 :: []))
            | NatMinus ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatMinus
                (e1 :: (e2 :: []))
            | NatMult ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatMult (e1 :: (e2 :: []))
            | NatDiv ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatDiv (e1 :: (e2 :: []))
            | NatRem ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatRem (e1 :: (e2 :: []))
            | NatMin ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatMinPair
                (e1 :: (e2 :: []))
            | NatMax ->
              mk_imp_ejson_runtime_call EJsonRuntimeNatMaxPair
                (e1 :: (e2 :: [])))
         | OpFloatBinary opa ->
           (match opa with
            | FloatPlus -> mk_imp_ejson_op EJsonOpAddNumber (e1 :: (e2 :: []))
            | FloatMinus -> mk_imp_ejson_op EJsonOpSub (e1 :: (e2 :: []))
            | FloatMult -> mk_imp_ejson_op EJsonOpMult (e1 :: (e2 :: []))
            | FloatDiv -> mk_imp_ejson_op EJsonOpDiv (e1 :: (e2 :: []))
            | FloatPow -> mk_imp_ejson_op EJsonOpMathPow (e1 :: (e2 :: []))
            | FloatMin -> mk_imp_ejson_op EJsonOpMathMin (e1 :: (e2 :: []))
            | FloatMax -> mk_imp_ejson_op EJsonOpMathMax (e1 :: (e2 :: [])))
         | OpFloatCompare opa ->
           (match opa with
            | FloatLt -> mk_imp_ejson_op EJsonOpLt (e1 :: (e2 :: []))
            | FloatLe -> mk_imp_ejson_op EJsonOpLe (e1 :: (e2 :: []))
            | FloatGt -> mk_imp_ejson_op EJsonOpGt (e1 :: (e2 :: []))
            | FloatGe -> mk_imp_ejson_op EJsonOpGe (e1 :: (e2 :: [])))
         | OpForeignBinary fb ->
           mk_imp_ejson_runtime_call (EJsonRuntimeForeign
             (fejtoruntime.foreign_to_ejson_runtime_of_binary_op fb)) el)
      | _ :: _ ->
        mk_imp_ejson_expr_error
          ('i'::('m'::('p'::('_'::('d'::('a'::('t'::('a'::('_'::('b'::('i'::('n'::('a'::('r'::('y'::('_'::('o'::('p'::('_'::('t'::('o'::('_'::('i'::('m'::('p'::('_'::('e'::('j'::('s'::('o'::('n'::(':'::(' '::('w'::('r'::('o'::('n'::('g'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val imp_data_op_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> imp_data_op -> ('a1, 'a2) imp_ejson_expr list ->
    ('a1, 'a2) imp_ejson_expr **)

let imp_data_op_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h op el =
  match op with
  | DataOpUnary op0 ->
    imp_data_unary_op_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h op0 el
  | DataOpBinary op0 ->
    imp_data_binary_op_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime op0 el

(** val imp_data_runtime_call_to_imp_ejson :
    imp_data_runtime_op -> ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2)
    imp_ejson_expr **)

let imp_data_runtime_call_to_imp_ejson op el =
  match op with
  | DataRuntimeGroupby (s, ls) ->
    mk_imp_ejson_runtime_call EJsonRuntimeGroupBy ((ImpExprConst
      (Coq_cejstring
      (key_encode s))) :: ((mk_string_array (map key_encode ls)) :: el))
  | DataRuntimeEither -> mk_either_expr el
  | DataRuntimeToLeft -> mk_to_left_expr el
  | DataRuntimeToRight -> mk_to_right_expr el

(** val imp_data_expr_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> imp_data_expr -> ('a1, 'a2) imp_ejson_expr **)

let rec imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h = function
| ImpExprError msg -> ImpExprError msg
| ImpExprVar v -> ImpExprVar v
| ImpExprConst d ->
  ejson_to_expr
    (data_to_ejson fruntime fejson fetojson
      (normalize_data fruntime.foreign_runtime_data h d))
| ImpExprOp (op, el) ->
  imp_data_op_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h
    op
    (map
      (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
        fejtoruntime h) el)
| ImpExprRuntimeCall (op, el) ->
  imp_data_runtime_call_to_imp_ejson op
    (map
      (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
        fejtoruntime h) el)

(** val imp_data_stmt_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> imp_data_stmt -> ('a1, 'a2) imp_ejson_stmt **)

let rec imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h = function
| ImpStmtBlock (lv, ls) ->
  ImpStmtBlock
    ((map (fun xy -> ((fst xy),
       (lift
         (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
           fejtoruntime h) (snd xy)))) lv),
    (map
      (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
        fejtoruntime h) ls))
| ImpStmtAssign (v, e) ->
  ImpStmtAssign (v,
    (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h e))
| ImpStmtFor (v, e, s) ->
  ImpStmtFor (v,
    (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h e),
    (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h s))
| ImpStmtForRange (v, e1, e2, s) ->
  ImpStmtForRange (v,
    (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h e1),
    (imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h e2),
    (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h s))
| ImpStmtIf (e, s1, s2) ->
  ImpStmtIf
    ((imp_data_expr_to_imp_ejson fruntime fejson fetojson fejruntime
       fejtoruntime h e),
    (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h s1),
    (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h s2))

(** val imp_data_function_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> imp_data_function -> ('a1, 'a2) imp_ejson_function **)

let imp_data_function_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h = function
| ImpFun (v, s, ret) ->
  ImpFun (v,
    (imp_data_stmt_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h s), ret)

(** val imp_data_to_imp_ejson :
    foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
    ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime
    -> brand_relation_t -> imp_data -> ('a1, 'a2) imp_ejson **)

let imp_data_to_imp_ejson fruntime fejson fetojson fejruntime fejtoruntime h i =
  map (fun decl ->
    let (name, def) = decl in
    (name,
    (imp_data_function_to_imp_ejson fruntime fejson fetojson fejruntime
      fejtoruntime h def))) i
