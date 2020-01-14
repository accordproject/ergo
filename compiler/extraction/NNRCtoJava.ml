open Assoc
open BinaryOperators
open BrandRelation
open CoqLibAdd
open Data
open Datatypes
open Digits
open EmitUtil
open EquivDec
open ForeignRuntime
open ForeignToJava
open Java
open List0
open NNRC
open Nat
open NativeString
open StringAdd
open ToString
open UnaryOperators
open Var
open CNNRC
open CNNRCShadow
open CNNRCVars

(** val unshadow_java :
    foreign_runtime -> var list -> NNRC.nnrc -> NNRC.nnrc **)

let unshadow_java fruntime avoid e =
  unshadow fruntime javaSafeSeparator javaIdentifierSanitize
    (app avoid javaAvoidList) e

(** val mk_java_json_brands : nstring -> brands -> java_json **)

let mk_java_json_brands quotel b =
  mk_java_json_array (map (mk_java_json_string quotel) (map nstring_quote b))

(** val mk_java_json_data :
    foreign_runtime -> foreign_to_java -> nstring -> data -> java_json **)

let rec mk_java_json_data fruntime ftojavajson quotel = function
| Coq_dunit -> java_json_NULL
| Coq_dnat n -> mk_java_json_nat quotel n
| Coq_dfloat n -> mk_java_json_number n
| Coq_dbool b -> mk_java_json_bool b
| Coq_dstring s -> mk_java_json_string quotel (nstring_quote s)
| Coq_dcoll ls ->
  mk_java_json_array (map (mk_java_json_data fruntime ftojavajson quotel) ls)
| Coq_drec ls ->
  mk_java_json_object quotel
    (map (fun kv ->
      let (k, v) = kv in
      ((nstring_quote k), (mk_java_json_data fruntime ftojavajson quotel v)))
      ls)
| Coq_dleft d0 ->
  mk_java_json_object quotel
    (((nstring_quote ('$'::('l'::('e'::('f'::('t'::[])))))),
    (mk_java_json_data fruntime ftojavajson quotel d0)) :: [])
| Coq_dright d0 ->
  mk_java_json_object quotel
    (((nstring_quote ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))),
    (mk_java_json_data fruntime ftojavajson quotel d0)) :: [])
| Coq_dbrand (b, d0) ->
  mk_java_json_object quotel
    (((nstring_quote ('$'::('d'::('a'::('t'::('a'::[])))))),
    (mk_java_json_data fruntime ftojavajson quotel d0)) :: (((nstring_quote
                                                               ('$'::('t'::('y'::('p'::('e'::[])))))),
    (mk_java_json_brands quotel b)) :: []))
| Coq_dforeign fd -> ftojavajson.foreign_to_java_data quotel fd

(** val uarithToJavaMethod : nat_arith_unary_op -> char list **)

let uarithToJavaMethod = function
| NatAbs -> 'a'::('b'::('s'::[]))
| NatLog2 -> 'l'::('o'::('g'::('2'::[])))
| NatSqrt -> 's'::('q'::('r'::('t'::[])))

(** val float_uarithToJavaMethod : float_arith_unary_op -> char list **)

let float_uarithToJavaMethod = function
| FloatNeg -> 'f'::('l'::('o'::('a'::('t'::('_'::('n'::('e'::('g'::[]))))))))
| FloatSqrt ->
  'f'::('l'::('o'::('a'::('t'::('_'::('s'::('q'::('r'::('t'::[])))))))))
| FloatExp -> 'f'::('l'::('o'::('a'::('t'::('_'::('e'::('x'::('p'::[]))))))))
| FloatLog -> 'f'::('l'::('o'::('a'::('t'::('_'::('l'::('o'::('g'::[]))))))))
| FloatLog10 ->
  'f'::('l'::('o'::('a'::('t'::('_'::('l'::('o'::('g'::('1'::('0'::[]))))))))))
| FloatCeil ->
  'f'::('l'::('o'::('a'::('t'::('_'::('c'::('e'::('i'::('l'::[])))))))))
| FloatFloor ->
  'f'::('l'::('o'::('a'::('t'::('_'::('f'::('l'::('o'::('o'::('r'::[]))))))))))
| FloatAbs -> 'f'::('l'::('o'::('a'::('t'::('_'::('a'::('b'::('s'::[]))))))))

(** val nat_barithToJavaMethod : nat_arith_binary_op -> char list **)

let nat_barithToJavaMethod = function
| NatPlus -> 'p'::('l'::('u'::('s'::[])))
| NatMinus -> 'm'::('i'::('n'::('u'::('s'::(' '::[])))))
| NatMult -> 'm'::('u'::('l'::('t'::[])))
| NatDiv -> 'd'::('i'::('v'::('i'::('d'::('e'::[])))))
| NatRem -> 'r'::('e'::('m'::[]))
| NatMin -> 'm'::('i'::('n'::[]))
| NatMax -> 'm'::('a'::('x'::[]))

(** val float_barithToJavaMethod : float_arith_binary_op -> char list **)

let float_barithToJavaMethod = function
| FloatPlus ->
  'f'::('l'::('o'::('a'::('t'::('_'::('p'::('l'::('u'::('s'::[])))))))))
| FloatMinus ->
  'f'::('l'::('o'::('a'::('t'::('_'::('m'::('i'::('n'::('u'::('s'::[]))))))))))
| FloatMult ->
  'f'::('l'::('o'::('a'::('t'::('_'::('m'::('u'::('l'::('t'::[])))))))))
| FloatDiv ->
  'f'::('l'::('o'::('a'::('t'::('_'::('d'::('i'::('v'::('i'::('d'::('e'::[])))))))))))
| FloatPow -> 'f'::('l'::('o'::('a'::('t'::('_'::('p'::('o'::('w'::[]))))))))
| FloatMin -> 'f'::('l'::('o'::('a'::('t'::('_'::('m'::('i'::('n'::[]))))))))
| FloatMax -> 'f'::('l'::('o'::('a'::('t'::('_'::('m'::('a'::('x'::[]))))))))

(** val float_bcompareToJavaMethod : float_compare_binary_op -> char list **)

let float_bcompareToJavaMethod = function
| FloatLt -> 'f'::('l'::('o'::('a'::('t'::('_'::('l'::('t'::[])))))))
| FloatLe -> 'f'::('l'::('o'::('a'::('t'::('_'::('l'::('e'::[])))))))
| FloatGt -> 'f'::('l'::('o'::('a'::('t'::('_'::('g'::('t'::[])))))))
| FloatGe -> 'f'::('l'::('o'::('a'::('t'::('_'::('g'::('e'::[])))))))

(** val like_clause_to_java : like_clause -> nstring **)

let like_clause_to_java = function
| Coq_like_literal literal ->
  nstring_append
    (nstring_quote
      ('n'::('e'::('w'::(' '::('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::('.'::('L'::('i'::('t'::('e'::('r'::('a'::('l'::('L'::('i'::('k'::('e'::('C'::('l'::('a'::('u'::('s'::('e'::('('::[]))))))))))))))))))))))))))))))))))))))
    (nstring_append (mk_java_string (nstring_quote literal))
      (nstring_quote (')'::[])))
| Coq_like_any_char ->
  nstring_quote
    ('n'::('e'::('w'::(' '::('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::('.'::('A'::('n'::('y'::('C'::('h'::('a'::('r'::('L'::('i'::('k'::('e'::('C'::('l'::('a'::('u'::('s'::('e'::('('::(')'::[]))))))))))))))))))))))))))))))))))))))
| Coq_like_any_string ->
  nstring_quote
    ('n'::('e'::('w'::(' '::('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::('.'::('A'::('n'::('y'::('S'::('t'::('r'::('i'::('n'::('g'::('L'::('i'::('k'::('e'::('C'::('l'::('a'::('u'::('s'::('e'::('('::(')'::[]))))))))))))))))))))))))))))))))))))))))

(** val nnrcToJava :
    foreign_runtime -> foreign_to_java -> NNRC.nnrc -> int -> int -> nstring
    -> nstring -> (char list * nstring) list -> (nstring * java_json) * int **)

let rec nnrcToJava fruntime ftojavajson n t i eol quotel ivs =
  match n with
  | NNRCGetConstant v ->
    (((nstring_quote []),
      (nstring_append (nstring_quote ('v'::[])) (nstring_quote v))), t)
  | NNRCVar v ->
    (match assoc_lookupr (equiv_dec string_eqdec) ivs v with
     | Some v_string -> (((nstring_quote []), v_string), t)
     | None ->
       (((nstring_quote []),
         (nstring_append (nstring_quote ('v'::[])) (nstring_quote v))), t))
  | NNRCConst d ->
    (((nstring_quote []), (mk_java_json_data fruntime ftojavajson quotel d)),
      t)
  | NNRCBinop (op, n1, n2) ->
    let (p, t2) = nnrcToJava fruntime ftojavajson n1 t i eol quotel ivs in
    let (s1, e1) = p in
    let (p0, t0) = nnrcToJava fruntime ftojavajson n2 t2 i eol quotel ivs in
    let (s2, e2) = p0 in
    let e0 =
      match op with
      | OpEqual ->
        mk_java_binary_op0
          (nstring_quote ('e'::('q'::('u'::('a'::('l'::('s'::[]))))))) e1 e2
      | OpRecConcat ->
        mk_java_binary_op0
          (nstring_quote ('c'::('o'::('n'::('c'::('a'::('t'::[]))))))) e1 e2
      | OpRecMerge ->
        mk_java_binary_op0
          (nstring_quote
            ('m'::('e'::('r'::('g'::('e'::('C'::('o'::('n'::('c'::('a'::('t'::[]))))))))))))
          e1 e2
      | OpAnd ->
        mk_java_binary_op0 (nstring_quote ('a'::('n'::('d'::[])))) e1 e2
      | OpOr -> mk_java_binary_op0 (nstring_quote ('o'::('r'::[]))) e1 e2
      | OpLt -> mk_java_binary_op0 (nstring_quote ('l'::('t'::[]))) e1 e2
      | OpLe -> mk_java_binary_op0 (nstring_quote ('l'::('e'::[]))) e1 e2
      | OpBagUnion ->
        mk_java_binary_op0
          (nstring_quote ('u'::('n'::('i'::('o'::('n'::[])))))) e1 e2
      | OpBagDiff ->
        mk_java_binary_op0
          (nstring_quote
            ('b'::('a'::('g'::('_'::('m'::('i'::('n'::('u'::('s'::[]))))))))))
          e1 e2
      | OpBagMin ->
        mk_java_binary_op0
          (nstring_quote ('b'::('a'::('g'::('_'::('m'::('i'::('n'::[]))))))))
          e1 e2
      | OpBagMax ->
        mk_java_binary_op0
          (nstring_quote ('b'::('a'::('g'::('_'::('m'::('a'::('x'::[]))))))))
          e1 e2
      | OpBagNth ->
        mk_java_binary_op0
          (nstring_quote ('b'::('a'::('g'::('_'::('n'::('t'::('h'::[]))))))))
          e1 e2
      | OpContains ->
        mk_java_binary_op0
          (nstring_quote
            ('c'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::[]))))))))) e1 e2
      | OpStringConcat ->
        mk_java_binary_op0
          (nstring_quote
            ('s'::('t'::('r'::('i'::('n'::('g'::('C'::('o'::('n'::('c'::('a'::('t'::[])))))))))))))
          e1 e2
      | OpStringJoin ->
        mk_java_binary_op0
          (nstring_quote
            ('s'::('t'::('r'::('i'::('n'::('g'::('J'::('o'::('i'::('n'::[])))))))))))
          e1 e2
      | OpNatBinary b ->
        mk_java_binary_op0 (nstring_quote (nat_barithToJavaMethod b)) e1 e2
      | OpFloatBinary b ->
        mk_java_binary_op0 (nstring_quote (float_barithToJavaMethod b)) e1 e2
      | OpFloatCompare b ->
        mk_java_binary_op0 (nstring_quote (float_bcompareToJavaMethod b)) e1
          e2
      | OpForeignBinary fb ->
        ftojavajson.foreign_to_java_binary_op i eol quotel fb e1 e2
    in
    (((nstring_append s1 s2), e0), t0)
  | NNRCUnop (op, n1) ->
    let (p, t0) = nnrcToJava fruntime ftojavajson n1 t i eol quotel ivs in
    let (s1, e1) = p in
    let e0 =
      match op with
      | OpIdentity -> e1
      | OpNeg -> mk_java_unary_op0 (nstring_quote ('n'::('e'::('g'::[])))) e1
      | OpRec s ->
        mk_java_unary_op1 (nstring_quote ('r'::('e'::('c'::[]))))
          (mk_java_string (nstring_quote s)) e1
      | OpDot s ->
        mk_java_unary_op1 (nstring_quote ('d'::('o'::('t'::[]))))
          (mk_java_string (nstring_quote s)) e1
      | OpRecRemove s ->
        mk_java_unary_op1
          (nstring_quote ('r'::('e'::('m'::('o'::('v'::('e'::[])))))))
          (mk_java_string (nstring_quote s)) e1
      | OpRecProject sl ->
        mk_java_unary_op1
          (nstring_quote ('p'::('r'::('o'::('j'::('e'::('c'::('t'::[]))))))))
          (mk_java_string_collection (map nstring_quote sl)) e1
      | OpBag ->
        mk_java_unary_op0 (nstring_quote ('c'::('o'::('l'::('l'::[]))))) e1
      | OpSingleton ->
        mk_java_unary_op0
          (nstring_quote
            ('s'::('i'::('n'::('g'::('l'::('e'::('t'::('o'::('n'::[]))))))))))
          e1
      | OpFlatten ->
        mk_java_unary_op0
          (nstring_quote ('f'::('l'::('a'::('t'::('t'::('e'::('n'::[]))))))))
          e1
      | OpDistinct ->
        mk_java_unary_op0
          (nstring_quote
            ('d'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::[]))))))))) e1
      | OpOrderBy sl ->
        mk_java_unary_op1 (nstring_quote ('s'::('o'::('r'::('t'::[])))))
          (mk_java_string_collection (map nstring_quote (map fst sl))) e1
      | OpCount ->
        mk_java_unary_op0
          (nstring_quote ('c'::('o'::('u'::('n'::('t'::[])))))) e1
      | OpToString ->
        mk_java_unary_op0
          (nstring_quote
            ('t'::('o'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))) e1
      | OpToText ->
        mk_java_unary_op0
          (nstring_quote ('t'::('o'::('t'::('e'::('x'::('t'::[]))))))) e1
      | OpLength ->
        mk_java_unary_op0
          (nstring_quote
            ('s'::('t'::('r'::('i'::('n'::('g'::('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))))))
          e1
      | OpSubstring (start, olen) ->
        (match olen with
         | Some len ->
           mk_java_unary_opn
             (nstring_quote
               ('s'::('u'::('b'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))
             (map nstring_quote
               (map (toString coq_ToString_Z) (start :: (len :: [])))) e1
         | None ->
           mk_java_unary_op1
             (nstring_quote
               ('s'::('u'::('b'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))
             (nstring_quote (toString coq_ToString_Z start)) e1)
      | OpLike pat ->
        let lc = make_like_clause pat None in
        mk_java_unary_op1
          (nstring_quote
            ('s'::('t'::('r'::('i'::('n'::('g'::('_'::('l'::('i'::('k'::('e'::[]))))))))))))
          (nstring_append
            (nstring_quote
              ('n'::('e'::('w'::(' '::('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::('.'::('L'::('i'::('k'::('e'::('C'::('l'::('a'::('u'::('s'::('e'::('['::(']'::('{'::[])))))))))))))))))))))))))))))))))
            (nstring_append
              (nstring_map_concat (nstring_quote (','::[]))
                like_clause_to_java lc) (nstring_quote ('}'::[])))) e1
      | OpLeft ->
        mk_java_unary_op0 (nstring_quote ('l'::('e'::('f'::('t'::[]))))) e1
      | OpRight ->
        mk_java_unary_op0
          (nstring_quote ('r'::('i'::('g'::('h'::('t'::[])))))) e1
      | OpBrand b ->
        mk_java_unary_op1
          (nstring_quote ('b'::('r'::('a'::('n'::('d'::[]))))))
          (mk_java_string_collection (map nstring_quote b)) e1
      | OpUnbrand ->
        mk_java_unary_op0
          (nstring_quote ('u'::('n'::('b'::('r'::('a'::('n'::('d'::[]))))))))
          e1
      | OpCast b ->
        mk_java_unary_opn (nstring_quote ('c'::('a'::('s'::('t'::[])))))
          ((nstring_quote
             ('i'::('n'::('h'::('e'::('r'::('i'::('t'::('a'::('n'::('c'::('e'::[])))))))))))) :: (
          (mk_java_string_collection (map nstring_quote b)) :: [])) e1
      | OpNatUnary u ->
        mk_java_unary_op0 (nstring_quote (uarithToJavaMethod u)) e1
      | OpNatSum ->
        mk_java_unary_op0 (nstring_quote ('s'::('u'::('m'::[])))) e1
      | OpNatMin ->
        mk_java_unary_op0
          (nstring_quote
            ('l'::('i'::('s'::('t'::('_'::('m'::('i'::('n'::[]))))))))) e1
      | OpNatMax ->
        mk_java_unary_op0
          (nstring_quote
            ('l'::('i'::('s'::('t'::('_'::('m'::('a'::('x'::[]))))))))) e1
      | OpNatMean ->
        mk_java_unary_op0
          (nstring_quote
            ('l'::('i'::('s'::('t'::('_'::('m'::('e'::('a'::('n'::[]))))))))))
          e1
      | OpFloatOfNat ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('o'::('f'::('_'::('i'::('n'::('t'::[])))))))))))))
          e1
      | OpFloatUnary u ->
        mk_java_unary_op0 (nstring_quote (float_uarithToJavaMethod u)) e1
      | OpFloatTruncate ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('t'::('r'::('u'::('n'::('c'::('a'::('t'::('e'::[])))))))))))))))
          e1
      | OpFloatSum ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('s'::('u'::('m'::[]))))))))))
          e1
      | OpFloatMean ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('l'::('i'::('s'::('t'::('_'::('m'::('e'::('a'::('n'::[]))))))))))))))))
          e1
      | OpFloatBagMin ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('l'::('i'::('s'::('t'::('_'::('m'::('i'::('n'::[])))))))))))))))
          e1
      | OpFloatBagMax ->
        mk_java_unary_op0
          (nstring_quote
            ('f'::('l'::('o'::('a'::('t'::('_'::('l'::('i'::('s'::('t'::('_'::('m'::('a'::('x'::[])))))))))))))))
          e1
      | OpForeignUnary fu ->
        ftojavajson.foreign_to_java_unary_op i eol quotel fu e1
    in
    ((s1, e0), t0)
  | NNRCLet (v, bind, body) ->
    let (p, t2) = nnrcToJava fruntime ftojavajson bind t i eol quotel ivs in
    let (s1, e1) = p in
    let (p0, t0) = nnrcToJava fruntime ftojavajson body t2 i eol quotel ivs in
    let (s2, e2) = p0 in
    let v0 = nstring_append (nstring_quote ('v'::[])) (nstring_quote v) in
    let ret =
      nstring_append
        (nstring_quote
          ('v'::('l'::('e'::('t'::('v'::('a'::('r'::('$'::[])))))))))
        (nstring_append (nstring_quote v)
          (nstring_append (nstring_quote ('$'::[]))
            (nstring_quote (nat_to_string10 t0))))
    in
    (((nstring_append s1
        (nstring_append (indent i)
          (nstring_append
            (nstring_quote
              ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
            (nstring_append ret
              (nstring_append (nstring_quote (';'::[]))
                (nstring_append eol
                  (nstring_append (indent i)
                    (nstring_append
                      (nstring_quote
                        ('{'::(' '::('/'::('/'::(' '::('n'::('e'::('w'::(' '::('s'::('c'::('o'::('p'::('e'::(' '::('i'::('n'::('t'::('r'::('o'::('d'::('u'::('c'::('e'::('d'::(' '::('f'::('o'::('r'::(' '::('a'::(' '::('l'::('e'::('t'::(' '::('s'::('t'::('a'::('t'::('e'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))
                      (nstring_append eol
                        (nstring_append (indent (add i (Pervasives.succ 0)))
                          (nstring_append
                            (nstring_quote
                              ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
                            (nstring_append v0
                              (nstring_append
                                (nstring_quote (' '::('='::(' '::[]))))
                                (nstring_append (from_java_json e1)
                                  (nstring_append (nstring_quote (';'::[]))
                                    (nstring_append eol
                                      (nstring_append s2
                                        (nstring_append
                                          (indent (add i (Pervasives.succ 0)))
                                          (nstring_append ret
                                            (nstring_append
                                              (nstring_quote
                                                (' '::('='::(' '::[]))))
                                              (nstring_append
                                                (from_java_json e2)
                                                (nstring_append
                                                  (nstring_quote (';'::[]))
                                                  (nstring_append eol
                                                    (nstring_append
                                                      (indent i)
                                                      (nstring_append
                                                        (nstring_quote
                                                          ('}'::[])) eol))))))))))))))))))))))))),
    ret), (add t0 (Pervasives.succ 0)))
  | NNRCFor (v, iter, body) ->
    let (p, t2) = nnrcToJava fruntime ftojavajson iter t i eol quotel ivs in
    let (s1, e1) = p in
    let (p0, t0) =
      nnrcToJava fruntime ftojavajson body t2 (add i (Pervasives.succ 0)) eol
        quotel ivs
    in
    let (s2, e2) = p0 in
    let elm = nstring_append (nstring_quote ('v'::[])) (nstring_quote v) in
    let src =
      nstring_append (nstring_quote ('s'::('r'::('c'::[]))))
        (nstring_quote (nat_to_string10 t0))
    in
    let idx =
      nstring_append (nstring_quote ('i'::[]))
        (nstring_quote (nat_to_string10 t0))
    in
    let dst =
      nstring_append (nstring_quote ('d'::('s'::('t'::[]))))
        (nstring_quote (nat_to_string10 t0))
    in
    (((nstring_append s1
        (nstring_append (indent i)
          (nstring_append
            (nstring_quote
              ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('A'::('r'::('r'::('a'::('y'::(' '::[])))))))))))))))))
            (nstring_append src
              (nstring_append
                (nstring_quote
                  (' '::('='::(' '::('('::('J'::('s'::('o'::('n'::('A'::('r'::('r'::('a'::('y'::(')'::(' '::[]))))))))))))))))
                (nstring_append (from_java_json e1)
                  (nstring_append (nstring_quote (';'::[]))
                    (nstring_append eol
                      (nstring_append (indent i)
                        (nstring_append
                          (nstring_quote
                            ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('A'::('r'::('r'::('a'::('y'::(' '::[])))))))))))))))))
                          (nstring_append dst
                            (nstring_append
                              (nstring_quote
                                (' '::('='::(' '::('n'::('e'::('w'::(' '::('J'::('s'::('o'::('n'::('A'::('r'::('r'::('a'::('y'::('('::(')'::(';'::[]))))))))))))))))))))
                              (nstring_append eol
                                (nstring_append (indent i)
                                  (nstring_append
                                    (nstring_quote
                                      ('f'::('o'::('r'::('('::('i'::('n'::('t'::(' '::[])))))))))
                                    (nstring_append idx
                                      (nstring_append
                                        (nstring_quote
                                          (' '::('='::(' '::('0'::(';'::(' '::[])))))))
                                        (nstring_append idx
                                          (nstring_append
                                            (nstring_quote
                                              (' '::('<'::(' '::[]))))
                                            (nstring_append src
                                              (nstring_append
                                                (nstring_quote
                                                  ('.'::('s'::('i'::('z'::('e'::('('::(')'::(';'::(' '::[]))))))))))
                                                (nstring_append idx
                                                  (nstring_append
                                                    (nstring_quote
                                                      ('+'::('+'::(')'::(' '::('{'::[]))))))
                                                    (nstring_append eol
                                                      (nstring_append
                                                        (indent
                                                          (add i
                                                            (Pervasives.succ
                                                            0)))
                                                        (nstring_append
                                                          (nstring_quote
                                                            ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
                                                          (nstring_append elm
                                                            (nstring_append
                                                              (nstring_quote
                                                                (' '::('='::(' '::[]))))
                                                              (nstring_append
                                                                src
                                                                (nstring_append
                                                                  (nstring_quote
                                                                    ('.'::('g'::('e'::('t'::('('::[]))))))
                                                                  (nstring_append
                                                                    idx
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (')'::(';'::[])))
                                                                    (nstring_append
                                                                    eol
                                                                    (nstring_append
                                                                    s2
                                                                    (nstring_append
                                                                    (indent
                                                                    (add i
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (nstring_append
                                                                    dst
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    ('.'::('a'::('d'::('d'::('('::[]))))))
                                                                    (nstring_append
                                                                    (from_java_json
                                                                    e2)
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (')'::(';'::[])))
                                                                    (nstring_append
                                                                    eol
                                                                    (nstring_append
                                                                    (indent i)
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    ('}'::[]))
                                                                    eol)))))))))))))))))))))))))))))))))))))))))),
    dst), (add t0 (Pervasives.succ 0)))
  | NNRCIf (c, n1, n2) ->
    let (p, t2) = nnrcToJava fruntime ftojavajson c t i eol quotel ivs in
    let (s1, e1) = p in
    let (p0, t3) =
      nnrcToJava fruntime ftojavajson n1 t2 (add i (Pervasives.succ 0)) eol
        quotel ivs
    in
    let (s2, e2) = p0 in
    let (p1, t0) =
      nnrcToJava fruntime ftojavajson n2 t3 (add i (Pervasives.succ 0)) eol
        quotel ivs
    in
    let (s3, e3) = p1 in
    let v0 =
      nstring_append (nstring_quote ('t'::[]))
        (nstring_quote (nat_to_string10 t0))
    in
    (((nstring_append s1
        (nstring_append (indent i)
          (nstring_append
            (nstring_quote
              ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
            (nstring_append v0
              (nstring_append (nstring_quote (';'::[]))
                (nstring_append eol
                  (nstring_append (indent i)
                    (nstring_append
                      (nstring_quote
                        ('i'::('f'::(' '::('('::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('a'::('s'::('B'::('o'::('o'::('l'::('e'::('a'::('n'::('('::[]))))))))))))))))))))))))))))
                      (nstring_append (from_java_json e1)
                        (nstring_append
                          (nstring_quote (')'::(')'::(' '::('{'::[])))))
                          (nstring_append eol
                            (nstring_append s2
                              (nstring_append
                                (indent (add i (Pervasives.succ 0)))
                                (nstring_append v0
                                  (nstring_append
                                    (nstring_quote (' '::('='::(' '::[]))))
                                    (nstring_append (from_java_json e2)
                                      (nstring_append
                                        (nstring_quote (';'::[]))
                                        (nstring_append eol
                                          (nstring_append (indent i)
                                            (nstring_append
                                              (nstring_quote
                                                ('}'::(' '::('e'::('l'::('s'::('e'::(' '::('{'::[])))))))))
                                              (nstring_append eol
                                                (nstring_append s3
                                                  (nstring_append
                                                    (indent
                                                      (add i (Pervasives.succ
                                                        0)))
                                                    (nstring_append v0
                                                      (nstring_append
                                                        (nstring_quote
                                                          (' '::('='::(' '::[]))))
                                                        (nstring_append
                                                          (from_java_json e3)
                                                          (nstring_append
                                                            (nstring_quote
                                                              (';'::[]))
                                                            (nstring_append
                                                              eol
                                                              (nstring_append
                                                                (indent i)
                                                                (nstring_append
                                                                  (nstring_quote
                                                                    ('}'::[]))
                                                                  eol)))))))))))))))))))))))))))))),
    v0), (add t0 (Pervasives.succ 0)))
  | NNRCEither (nd, xl, nl, xr, nr) ->
    let (p, t2) = nnrcToJava fruntime ftojavajson nd t i eol quotel ivs in
    let (s1, e1) = p in
    let (p0, t1) =
      nnrcToJava fruntime ftojavajson nl t2 (add i (Pervasives.succ 0)) eol
        quotel ivs
    in
    let (s2, e2) = p0 in
    let (p1, t0) =
      nnrcToJava fruntime ftojavajson nr t1 (add i (Pervasives.succ 0)) eol
        quotel ivs
    in
    let (s3, e3) = p1 in
    let vl = nstring_append (nstring_quote ('v'::[])) (nstring_quote xl) in
    let vr = nstring_append (nstring_quote ('v'::[])) (nstring_quote xr) in
    let res =
      nstring_append (nstring_quote ('r'::('e'::('s'::[]))))
        (nstring_quote (nat_to_string10 t0))
    in
    (((nstring_append s1
        (nstring_append (indent i)
          (nstring_append
            (nstring_quote
              ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
            (nstring_append res
              (nstring_append (nstring_quote (';'::[]))
                (nstring_append eol
                  (nstring_append (indent i)
                    (nstring_append
                      (nstring_quote
                        ('i'::('f'::(' '::('('::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('e'::('i'::('t'::('h'::('e'::('r'::('('::[])))))))))))))))))))))))))
                      (nstring_append (from_java_json e1)
                        (nstring_append
                          (nstring_quote (')'::(')'::(' '::('{'::[])))))
                          (nstring_append eol
                            (nstring_append
                              (indent (add i (Pervasives.succ 0)))
                              (nstring_append
                                (nstring_quote
                                  ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
                                (nstring_append vl
                                  (nstring_append eol
                                    (nstring_append
                                      (indent (add i (Pervasives.succ 0)))
                                      (nstring_append
                                        (nstring_quote
                                          (' '::('='::(' '::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('t'::('o'::('L'::('e'::('f'::('t'::('('::[]))))))))))))))))))))))))
                                        (nstring_append (from_java_json e1)
                                          (nstring_append
                                            (nstring_quote (')'::(';'::[])))
                                            (nstring_append eol
                                              (nstring_append s2
                                                (nstring_append
                                                  (indent
                                                    (add i (Pervasives.succ
                                                      0)))
                                                  (nstring_append res
                                                    (nstring_append
                                                      (nstring_quote
                                                        (' '::('='::(' '::[]))))
                                                      (nstring_append
                                                        (from_java_json e2)
                                                        (nstring_append
                                                          (nstring_quote
                                                            (';'::[]))
                                                          (nstring_append eol
                                                            (nstring_append
                                                              (indent i)
                                                              (nstring_append
                                                                (nstring_quote
                                                                  ('}'::(' '::('e'::('l'::('s'::('e'::(' '::('{'::[])))))))))
                                                                (nstring_append
                                                                  eol
                                                                  (nstring_append
                                                                    (indent
                                                                    (add i
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    ('f'::('i'::('n'::('a'::('l'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))))))))
                                                                    (nstring_append
                                                                    vr
                                                                    (nstring_append
                                                                    eol
                                                                    (nstring_append
                                                                    (indent
                                                                    (add i
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (' '::('='::(' '::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('t'::('o'::('R'::('i'::('g'::('h'::('t'::('('::[])))))))))))))))))))))))))
                                                                    (nstring_append
                                                                    (from_java_json
                                                                    e1)
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (')'::(';'::[])))
                                                                    (nstring_append
                                                                    eol
                                                                    (nstring_append
                                                                    s3
                                                                    (nstring_append
                                                                    (indent
                                                                    (add i
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (nstring_append
                                                                    res
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (' '::('='::(' '::[]))))
                                                                    (nstring_append
                                                                    (from_java_json
                                                                    e3)
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    (';'::[]))
                                                                    (nstring_append
                                                                    eol
                                                                    (nstring_append
                                                                    (indent i)
                                                                    (nstring_append
                                                                    (nstring_quote
                                                                    ('}'::[]))
                                                                    eol)))))))))))))))))))))))))))))))))))))))))))))))),
    res), (add t0 (Pervasives.succ 0)))
  | NNRCGroupBy (g, sl, n1) ->
    let (p, t0) = nnrcToJava fruntime ftojavajson n1 t i eol quotel ivs in
    let (s1, e1) = p in
    let e0 =
      mk_java_unary_opn
        (nstring_quote ('g'::('r'::('o'::('u'::('p'::('b'::('y'::[]))))))))
        ((mk_java_string (nstring_quote g)) :: ((mk_java_string_collection
                                                  (map nstring_quote sl)) :: []))
        e1
    in
    ((s1, e0), t0)

(** val nnrcToJavaunshadow :
    foreign_runtime -> foreign_to_java -> NNRC.nnrc -> int -> int -> nstring
    -> nstring -> var list -> (char list * nstring) list ->
    (nstring * java_json) * int **)

let nnrcToJavaunshadow fruntime ftojavajson n t i eol quotel avoid ivs =
  let n0 = unshadow_java fruntime avoid n in
  nnrcToJava fruntime ftojavajson n0 t i eol quotel ivs

(** val makeJavaParams : (char list * nstring) list -> nstring **)

let makeJavaParams ivs =
  nstring_map_concat (nstring_quote (','::(' '::[]))) (fun elem ->
    nstring_append
      (nstring_quote
        ('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[])))))))))))))
      (snd elem)) ivs

(** val closeFreeVars :
    foreign_runtime -> char list -> NNRC.nnrc -> (char list * nstring) list
    -> NNRC.nnrc **)

let closeFreeVars fruntime input e ivs =
  let all_free_vars = nnrc_global_vars fruntime e in
  let wrap_one_free_var = fun e' fv ->
    match assoc_lookupr (equiv_dec string_eqdec) ivs fv with
    | Some _ -> e'
    | None -> NNRCLet (fv, (NNRCUnop ((OpDot fv), (NNRCVar input))), e')
  in
  fold_left wrap_one_free_var all_free_vars e

(** val nnrcToJavaFun :
    foreign_runtime -> foreign_to_java -> int -> char list -> NNRC.nnrc ->
    nstring -> nstring -> (char list * nstring) list -> nstring -> nstring **)

let nnrcToJavaFun fruntime ftojavajson i input_v e eol quotel ivs fname =
  let e' = closeFreeVars fruntime input_v e ivs in
  let (p, _) =
    nnrcToJavaunshadow fruntime ftojavajson e' (Pervasives.succ 0)
      (add i (Pervasives.succ 0)) eol quotel
      (('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::('s'::[]))))))))) :: (('i'::('n'::('h'::('e'::('r'::('i'::('t'::('a'::('n'::('c'::('e'::[]))))))))))) :: 
      (map fst ivs))) ivs
  in
  let (j0, v0) = p in
  nstring_append (indent i)
    (nstring_append
      (nstring_quote
        ('p'::('u'::('b'::('l'::('i'::('c'::(' '::('J'::('s'::('o'::('n'::('E'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::[]))))))))))))))))))))
      (nstring_append fname
        (nstring_append
          (nstring_quote
            ('('::('I'::('n'::('h'::('e'::('r'::('i'::('t'::('a'::('n'::('c'::('e'::(' '::('i'::('n'::('h'::('e'::('r'::('i'::('t'::('a'::('n'::('c'::('e'::(','::(' '::[])))))))))))))))))))))))))))
          (nstring_append (makeJavaParams ivs)
            (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
              (nstring_append eol
                (nstring_append j0
                  (nstring_append (indent i)
                    (nstring_append
                      (nstring_quote
                        (' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::[]))))))))))
                      (nstring_append (from_java_json v0)
                        (nstring_append (nstring_quote (';'::[]))
                          (nstring_append eol
                            (nstring_append (indent i)
                              (nstring_append (nstring_quote ('}'::[])) eol))))))))))))))
