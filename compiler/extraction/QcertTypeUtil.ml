open Ast
open BinaryOperators
open NamespaceContext
open PrintTypedData
open Provenance
open QcertType
open RType
open Result0
open String0
open TBrandModel
open UnaryOperators

(** val empty_rec_type : brand_model -> QLib.qcert_type **)

let empty_rec_type m =
  coq_Rec enhanced_foreign_type m.brand_model_relation Closed []

(** val ergo_format_unop_error :
    brand_model -> namespace_ctxt -> unary_op -> QLib.qcert_type -> char list **)

let ergo_format_unop_error m nsctxt op arg =
  let fmt_easy = fun name expected actual ->
    append
      ('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('`'::[]))))))))))
      (append name
        (append
          ('\''::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))
          (append (qcert_type_to_string m nsctxt expected)
            (append
              ('\''::(' '::('b'::('u'::('t'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))
              (append (qcert_type_to_string m nsctxt actual)
                ('\''::('.'::[])))))))
  in
  (match op with
   | OpIdentity ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpNeg ->
     fmt_easy ('!'::[]) (QLib.QcertType.tbool m.brand_model_relation) arg
   | OpRec _ ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpDot name ->
     append
       ('T'::('h'::('e'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('`'::[])))))))))))
       (append name
         (append
           ('\''::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('i'::('s'::('t'::(' '::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))))
           (append (qcert_type_to_string m nsctxt arg) ('\''::[]))))
   | OpBag ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpLeft ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpRight ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpBrand _ ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpUnbrand ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpCast _ ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[]))
   | OpFloatUnary f ->
     (match f with
      | FloatNeg ->
        fmt_easy ('-'::[]) (QLib.QcertType.tfloat m.brand_model_relation) arg
      | _ ->
        append
          ('T'::('h'::('i'::('s'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (append (qcert_type_to_string m nsctxt arg) ('\''::[])))
   | _ ->
     append
       ('T'::('h'::('i'::('s'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg) ('\''::[])))

(** val ergo_format_binop_error :
    brand_model -> namespace_ctxt -> binary_op -> QLib.qcert_type ->
    QLib.qcert_type -> char list **)

let ergo_format_binop_error m nsctxt op arg1 arg2 =
  let fmt_easy = fun name e1 e2 ->
    append
      ('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('`'::[]))))))))))
      (append name
        (append
          ('\''::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))
          (append (qcert_type_to_string m nsctxt e1)
            (append ('\''::(' '::('a'::('n'::('d'::(' '::('`'::[])))))))
              (append (qcert_type_to_string m nsctxt e2)
                (append
                  ('\''::(' '::('b'::('u'::('t'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))
                  (append (qcert_type_to_string m nsctxt arg1)
                    (append
                      ('\''::(' '::('a'::('n'::('d'::(' '::('`'::[])))))))
                      (append (qcert_type_to_string m nsctxt arg2)
                        ('\''::('.'::[])))))))))))
  in
  (match op with
   | OpEqual ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))
   | OpRecConcat ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))
   | OpRecMerge ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))
   | OpAnd ->
     fmt_easy ('a'::('n'::('d'::[])))
       (QLib.QcertType.tbool m.brand_model_relation)
       (QLib.QcertType.tbool m.brand_model_relation)
   | OpOr ->
     fmt_easy ('o'::('r'::[])) (QLib.QcertType.tbool m.brand_model_relation)
       (QLib.QcertType.tbool m.brand_model_relation)
   | OpLt ->
     fmt_easy ('<'::[]) (QLib.QcertType.tnat m.brand_model_relation)
       (QLib.QcertType.tnat m.brand_model_relation)
   | OpLe ->
     fmt_easy ('<'::('='::[])) (QLib.QcertType.tnat m.brand_model_relation)
       (QLib.QcertType.tnat m.brand_model_relation)
   | OpStringConcat ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))
   | OpStringJoin ->
     append
       ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))
   | OpNatBinary natPow ->
     (match natPow with
      | NatPlus ->
        fmt_easy ('+'::[]) (QLib.QcertType.tnat m.brand_model_relation)
          (QLib.QcertType.tnat m.brand_model_relation)
      | NatMinus ->
        fmt_easy ('-'::[]) (QLib.QcertType.tnat m.brand_model_relation)
          (QLib.QcertType.tnat m.brand_model_relation)
      | NatMult ->
        fmt_easy ('*'::[]) (QLib.QcertType.tnat m.brand_model_relation)
          (QLib.QcertType.tnat m.brand_model_relation)
      | NatDiv ->
        fmt_easy ('/'::[]) (QLib.QcertType.tnat m.brand_model_relation)
          (QLib.QcertType.tnat m.brand_model_relation)
      | _ ->
        fmt_easy ('^'::[]) (QLib.QcertType.tnat m.brand_model_relation)
          (QLib.QcertType.tnat m.brand_model_relation))
   | OpFloatBinary f ->
     (match f with
      | FloatPlus ->
        fmt_easy ('+'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatMinus ->
        fmt_easy ('-'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatMult ->
        fmt_easy ('*'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatDiv ->
        fmt_easy ('/'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatPow ->
        fmt_easy ('^'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | _ ->
        append
          ('T'::('h'::('i'::('s'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
          (append (qcert_type_to_string m nsctxt arg1)
            (append ('\''::(' '::[]))
              (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
                (append (qcert_type_to_string m nsctxt arg2)
                  ('\''::('.'::[])))))))
   | OpFloatCompare f ->
     (match f with
      | FloatLt ->
        fmt_easy ('<'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatLe ->
        fmt_easy ('<'::('='::[]))
          (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatGt ->
        fmt_easy ('>'::[]) (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation)
      | FloatGe ->
        fmt_easy ('>'::('='::[]))
          (QLib.QcertType.tfloat m.brand_model_relation)
          (QLib.QcertType.tfloat m.brand_model_relation))
   | _ ->
     append
       ('T'::('h'::('i'::('s'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
       (append (qcert_type_to_string m nsctxt arg1)
         (append ('\''::(' '::[]))
           (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
             (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[])))))))

(** val ergo_format_as_operator_dispatch_error :
    brand_model -> namespace_ctxt -> QLib.qcert_type -> char list **)

let ergo_format_as_operator_dispatch_error m nsctxt arg =
  append
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('u'::('s'::('e'::(' '::('\''::('a'::('s'::('\''::(' '::('o'::('n'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))))))))))))))
    (append (qcert_type_to_string m nsctxt arg) ('\''::('.'::[])))

(** val ergo_format_unary_operator_dispatch_error :
    brand_model -> namespace_ctxt -> ergo_unary_operator -> QLib.qcert_type
    -> char list **)

let ergo_format_unary_operator_dispatch_error m nsctxt _ arg =
  append
    ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (append (qcert_type_to_string m nsctxt arg) ('\''::('.'::[])))

(** val ergo_format_binary_operator_dispatch_error :
    brand_model -> namespace_ctxt -> ergo_binary_operator -> QLib.qcert_type
    -> QLib.qcert_type -> char list **)

let ergo_format_binary_operator_dispatch_error m nsctxt _ arg1 arg2 =
  append
    ('T'::('h'::('i'::('s'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::('d'::(' '::('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
    (append (qcert_type_to_string m nsctxt arg1)
      (append ('\''::(' '::[]))
        (append (' '::('a'::('n'::('d'::(' '::('`'::[]))))))
          (append (qcert_type_to_string m nsctxt arg2) ('\''::('.'::[]))))))

(** val ergo_format_new_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type -> char list **)

let ergo_format_new_error m nsctxt name actual =
  let concept_name =
    qcert_type_to_string m nsctxt
      (coq_Brand enhanced_foreign_type m.brand_model_relation (name :: []))
  in
  (match QLib.QcertType.diff_record_types m (name :: []) actual with
   | Some p ->
     let (expected_names, actual_names) = p in
     (match expected_names with
      | [] ->
        (match actual_names with
         | [] ->
           (match QLib.QcertType.fields_that_are_not_subtype m (name :: [])
                    actual with
            | [] ->
              append
                ('C'::('o'::('n'::('c'::('e'::('p'::('t'::(' '::[]))))))))
                (append name
                  (' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('d'::('a'::('t'::('a'::(' '::('('::('o'::('n'::('e'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('s'::('u'::('b'::('t'::('y'::('p'::('e'::(')'::[])))))))))))))))))))))))))))))))))))))))))))))))))
            | p0 :: _ ->
              let (p1, actual_type) = p0 in
              let (expected_name, expected_type) = p1 in
              append ('F'::('i'::('e'::('l'::('d'::(' '::('`'::[])))))))
                (append expected_name
                  (append
                    ('\''::(' '::('h'::('a'::('s'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))
                    (append (qcert_type_to_string m nsctxt actual_type)
                      (append
                        ('\''::(' '::('b'::('u'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[]))))))))))))))))))))))))
                        (append (qcert_type_to_string m nsctxt expected_type)
                          ('\''::[])))))))
         | actual_name :: l ->
           (match l with
            | [] ->
              append
                ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('`'::[])))))))))))))))
                (append actual_name
                  (append
                    ('\''::(' '::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))
                    (append concept_name ('\''::[]))))
            | _ :: _ ->
              append
                ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('i'::('e'::('l'::('d'::('s'::(' '::('`'::[]))))))))))))))))
                (append (concat ('\''::(','::(' '::('`'::[])))) actual_names)
                  (append
                    ('\''::(' '::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))
                    (append concept_name ('\''::[]))))))
      | expected_name :: l ->
        (match l with
         | [] ->
           append
             ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('`'::[])))))))))))))))
             (append expected_name
               (append
                 ('\''::(' '::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))
                 (append concept_name ('\''::[]))))
         | _ :: _ ->
           append
             ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('f'::('i'::('e'::('l'::('d'::('s'::(' '::('`'::[]))))))))))))))))
             (append (concat ('\''::(','::(' '::('`'::[])))) expected_names)
               (append
                 ('\''::(' '::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('`'::[])))))))))))
                 (append concept_name ('\''::[]))))))
   | None ->
     append
       ('C'::('o'::('n'::('c'::('e'::('p'::('t'::(' '::('n'::('a'::('m'::('e'::(' '::[])))))))))))))
       (append name
         (' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('d'::('a'::('t'::('a'::[]))))))))))))))))))))))

(** val ergo_format_clause_return_fallback_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
    QLib.qcert_type -> char list **)

let ergo_format_clause_return_fallback_error m nsctxt name actual expected =
  let actual_s = qcert_type_to_string m nsctxt actual in
  let expected_s = qcert_type_to_string m nsctxt expected in
  append ('C'::('l'::('a'::('u'::('s'::('e'::(' '::[])))))))
    (append name
      (append
        (' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('`'::[]))))))))))))))))
        (append expected_s
          (append
            ('\''::(' '::('b'::('u'::('t'::(' '::('a'::('c'::('t'::('u'::('a'::('l'::('l'::('y'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('s'::(' '::('`'::[]))))))))))))))))))))))))
            (append actual_s ('\''::[]))))))

(** val ergo_format_clause_return_component_error :
    brand_model -> namespace_ctxt -> char list -> char list -> char list ->
    QLib.qcert_type -> QLib.qcert_type -> char list **)

let ergo_format_clause_return_component_error m nsctxt name component1 component2 actual expected =
  let actual_s = qcert_type_to_string m nsctxt actual in
  let expected_s = qcert_type_to_string m nsctxt expected in
  append ('C'::('l'::('a'::('u'::('s'::('e'::(' '::[])))))))
    (append name
      (append (' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::[]))))))))
        (append component1
          (append (' '::('`'::[]))
            (append expected_s
              (append
                ('\''::(' '::('b'::('u'::('t'::(' '::('a'::('c'::('t'::('u'::('a'::('l'::('l'::('y'::(' '::[])))))))))))))))
                (append component2
                  (append (' '::('`'::[])) (append actual_s ('\''::[]))))))))))

(** val ergo_format_clause_return_normal_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
    QLib.qcert_type ->
    (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
    ->
    (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
    -> char list **)

let ergo_format_clause_return_normal_error m nsctxt name actual expected actual_quad expected_quad =
  let (p, actual_error) = actual_quad in
  let (p0, actual_state) = p in
  let (actual_resp, actual_emit) = p0 in
  let (p1, expected_error) = expected_quad in
  let (p2, expected_state) = p1 in
  let (expected_resp, expected_emit) = p2 in
  if QLib.QcertType.qcert_type_subtype_dec m actual_resp expected_resp
  then if QLib.QcertType.qcert_type_subtype_dec m actual_emit expected_emit
       then if QLib.QcertType.qcert_type_subtype_dec m actual_state
                 expected_state
            then if QLib.QcertType.qcert_type_subtype_dec m actual_error
                      expected_error
                 then ergo_format_clause_return_fallback_error m nsctxt name
                        actual expected
                 else ergo_format_clause_return_component_error m nsctxt name
                        ('f'::('a'::('i'::('l'::(' '::('w'::('i'::('t'::('h'::[])))))))))
                        ('f'::('a'::('i'::('l'::('s'::(' '::('w'::('i'::('t'::('h'::[]))))))))))
                        actual_error expected_error
            else ergo_format_clause_return_component_error m nsctxt name
                   ('s'::('e'::('t'::(' '::('s'::('t'::('a'::('t'::('e'::[])))))))))
                   ('s'::('e'::('t'::('s'::(' '::('s'::('t'::('a'::('t'::('e'::[]))))))))))
                   actual_state expected_state
       else ergo_format_clause_return_component_error m nsctxt name
              ('e'::('m'::('i'::('t'::[]))))
              ('e'::('m'::('i'::('t'::('s'::[]))))) actual_emit expected_emit
  else ergo_format_clause_return_component_error m nsctxt name
         ('r'::('e'::('s'::('p'::('o'::('n'::('d'::[])))))))
         ('r'::('e'::('s'::('p'::('o'::('n'::('d'::('s'::[]))))))))
         actual_resp expected_resp

(** val ergo_format_clause_return_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
    QLib.qcert_type -> char list **)

let ergo_format_clause_return_error m nsctxt name actual expected =
  let actual_quad = unpack_output_type m nsctxt actual [] in
  let expected_quad = unpack_output_type m nsctxt expected [] in
  let normal_error =
    ergo_format_clause_return_normal_error m nsctxt name actual expected
  in
  let fallback_error = fun _ ->
    ergo_format_clause_return_fallback_error m nsctxt name actual expected
  in
  elift2_both normal_error fallback_error actual_quad expected_quad

(** val ergo_format_function_return_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type ->
    QLib.qcert_type -> char list **)

let ergo_format_function_return_error m nsctxt name actual expected =
  let actual_s = qcert_type_to_string m nsctxt actual in
  let expected_s = qcert_type_to_string m nsctxt expected in
  append ('F'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[])))))))))
    (append name
      (append
        (' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('`'::[]))))))))))))))))
        (append expected_s
          (append
            ('\''::(' '::('b'::('u'::('t'::(' '::('a'::('c'::('t'::('u'::('a'::('l'::('l'::('y'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('s'::(' '::('`'::[]))))))))))))))))))))))))
            (append actual_s ('\''::[]))))))

(** val make_unary_operator_criteria :
    brand_model -> unary_op -> namespace_ctxt -> provenance ->
    QLib.QcertType.qtype -> QLib.qcert_type eresult **)

let make_unary_operator_criteria m op nsctxt prov t =
  match QLib.QcertType.qcert_type_infer_unary_op m op t with
  | Some p -> let (r, _) = p in esuccess r []
  | None ->
    efailure (ETypeError (prov, (ergo_format_unop_error m nsctxt op t)))

(** val make_binary_operator_criteria :
    brand_model -> binary_op -> namespace_ctxt -> provenance ->
    QLib.QcertType.qtype -> QLib.QcertType.qtype -> QLib.qcert_type eresult **)

let make_binary_operator_criteria m op nsctxt prov t1 t2 =
  match QLib.QcertType.qcert_type_infer_binary_op m op t1 t2 with
  | Some p -> let (p0, _) = p in let (r, _) = p0 in esuccess r []
  | None ->
    efailure (ETypeError (prov, (ergo_format_binop_error m nsctxt op t1 t2)))
