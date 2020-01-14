open Ast
open BinaryOperators
open Data
open DateTimeComponent
open Ergo
open ErgoCT
open MonetaryAmountComponent
open Names
open NamespaceContext
open Provenance
open QcertData
open QcertType
open QcertTypeUtil
open QcertTyping
open RType
open Result0
open TBrandModel
open UnaryOperators

type unary_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type
  eresult) * (provenance -> QLib.qcert_type -> ergoct_expr -> ergoct_expr)

type unary_dispatch_table = unary_dispatch_spec list

(** val make_unary_operator_fun :
    brand_model -> QLib.QcertOps.Unary.op -> provenance -> QLib.qcert_type ->
    (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    ergoct_expr **)

let make_unary_operator_fun _ op0 prov t e =
  EUnaryBuiltin ((prov, t), op0, e)

(** val make_unary_operator :
    brand_model -> unary_op -> unary_dispatch_spec **)

let make_unary_operator m op0 =
  ((make_unary_operator_criteria m op0), (make_unary_operator_fun m op0))

(** val make_nat_minus_fun :
    brand_model -> provenance -> QLib.QcertType.qtype ->
    (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr
    -> ergoct_expr **)

let make_nat_minus_fun m prov t e =
  EBinaryBuiltin ((prov, t), (OpNatBinary NatMinus), (EConst ((prov,
    (QLib.QcertType.tnat m.brand_model_relation)), (Coq_dnat 0))), e)

(** val make_nat_minus_criteria :
    brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
    QLib.qcert_type eresult **)

let make_nat_minus_criteria m nsctxt prov t =
  match QLib.QcertType.qcert_type_infer_binary_op m (OpNatBinary NatMinus)
          (QLib.QcertType.tnat m.brand_model_relation) t with
  | Some p -> let (p0, _) = p in let (r, _) = p0 in esuccess r []
  | None ->
    efailure (ETypeError (prov,
      (ergo_format_binop_error m nsctxt (OpNatBinary NatMinus)
        (QLib.QcertType.tnat m.brand_model_relation) t)))

(** val make_nat_minus_operator : brand_model -> unary_dispatch_spec **)

let make_nat_minus_operator m =
  ((make_nat_minus_criteria m), (make_nat_minus_fun m))

(** val make_dot_criteria :
    brand_model -> char list -> namespace_ctxt -> provenance ->
    QLib.QcertType.qtype -> QLib.qcert_type eresult **)

let make_dot_criteria m name nsctxt prov t =
  match QLib.QcertType.qcert_type_infer_unary_op m (OpDot name) t with
  | Some p -> let (r, _) = p in esuccess r []
  | None ->
    efailure (ETypeError (prov,
      (ergo_format_unop_error m nsctxt (OpDot name) t)))

(** val make_dot_operator :
    brand_model -> char list -> unary_dispatch_spec **)

let make_dot_operator m name =
  ((make_dot_criteria m name), (make_unary_operator_fun m (OpDot name)))

(** val make_unbrand_dot_fun :
    brand_model -> char list -> provenance -> QLib.qcert_type ->
    (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    ergoct_expr **)

let make_unbrand_dot_fun _ name prov t e =
  EUnaryBuiltin ((prov, t), (OpDot name), (EUnaryBuiltin ((prov, t),
    OpUnbrand, e)))

(** val make_unbrand_dot_criteria :
    brand_model -> char list -> namespace_ctxt -> provenance ->
    QLib.QcertType.qtype -> QLib.qcert_type eresult **)

let make_unbrand_dot_criteria m name nsctxt prov t =
  match QLib.QcertType.qcert_type_infer_unary_op m OpUnbrand t with
  | Some p ->
    let (r1, _) = p in
    (match QLib.QcertType.qcert_type_infer_unary_op m (OpDot name) r1 with
     | Some p0 -> let (r2, _) = p0 in esuccess r2 []
     | None ->
       efailure (ETypeError (prov,
         (ergo_format_unop_error m nsctxt (OpDot name) t))))
  | None ->
    efailure (ESystemError (prov,
      ('W'::('R'::('O'::('N'::('G'::(' '::('K'::('I'::('N'::('D'::[]))))))))))))

(** val make_unbrand_dot_operator :
    brand_model -> char list -> unary_dispatch_spec **)

let make_unbrand_dot_operator m name =
  ((make_unbrand_dot_criteria m name), (make_unbrand_dot_fun m name))

(** val unary_operator_dispatch_table :
    brand_model -> ergo_unary_operator -> unary_dispatch_table **)

let unary_operator_dispatch_table m = function
| EOpUMinus ->
  (make_unary_operator m (OpFloatUnary FloatNeg)) :: ((make_nat_minus_operator
                                                        m) :: [])
| EOpDot name ->
  (make_unbrand_dot_operator m name) :: ((make_dot_operator m name) :: [])

(** val try_unary_dispatch :
    brand_model -> namespace_ctxt -> provenance -> eerror ->
    ergo_unary_operator -> unary_dispatch_table -> ergoct_expr -> ergoct_expr
    eresult **)

let rec try_unary_dispatch m nsctxt prov prev eop bltops eT =
  let t = exprct_type_annot m eT in
  (match bltops with
   | [] ->
     efailure (ETypeError (prov,
       (ergo_format_unary_operator_dispatch_error m nsctxt eop t)))
   | u :: bltops' ->
     let (op_criteria, op_fun) = u in
     (match bltops' with
      | [] ->
        elift_both (fun r -> esuccess (op_fun prov r eT) []) (fun err ->
          match err with
          | ESystemError (_, _) -> efailure prev
          | _ -> efailure err) (op_criteria nsctxt prov t)
      | _ :: _ ->
        elift_both (fun r -> esuccess (op_fun prov r eT) []) (fun err ->
          try_unary_dispatch m nsctxt prov err eop bltops' eT)
          (op_criteria nsctxt prov t)))

(** val unary_dispatch :
    brand_model -> namespace_ctxt -> provenance -> ergo_unary_operator ->
    ergoct_expr -> ergoct_expr eresult **)

let unary_dispatch m nsctxt prov eop eT =
  let t = exprct_type_annot m eT in
  let init_prev = ETypeError (prov,
    (ergo_format_unary_operator_dispatch_error m nsctxt eop t))
  in
  try_unary_dispatch m nsctxt prov init_prev eop
    (unary_operator_dispatch_table m eop) eT

type binary_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type ->
  QLib.qcert_type eresult) * (provenance -> QLib.qcert_type -> ergoct_expr ->
  ergoct_expr -> ergoct_expr)

type binary_dispatch_table = binary_dispatch_spec list

(** val make_binary_operator_fun :
    brand_model -> QLib.QcertOps.Binary.op -> provenance -> QLib.qcert_type
    -> (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    ergoct_expr **)

let make_binary_operator_fun _ op0 prov t e1 e2 =
  EBinaryBuiltin ((prov, t), op0, e1, e2)

(** val make_binary_operator :
    brand_model -> binary_op -> binary_dispatch_spec **)

let make_binary_operator m op0 =
  ((make_binary_operator_criteria m op0), (make_binary_operator_fun m op0))

(** val make_neg_binary_operator_fun :
    brand_model -> QLib.QcertOps.Binary.op -> provenance -> QLib.qcert_type
    -> (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    ergoct_expr **)

let make_neg_binary_operator_fun _ op0 prov t e1 e2 =
  EUnaryBuiltin ((prov, t), OpNeg, (EBinaryBuiltin ((prov, t), op0, e1, e2)))

(** val make_neg_binary_operator :
    brand_model -> binary_op -> binary_dispatch_spec **)

let make_neg_binary_operator m op0 =
  ((make_binary_operator_criteria m op0),
    (make_neg_binary_operator_fun m op0))

(** val binary_operator_dispatch_table :
    brand_model -> ergo_binary_operator -> binary_dispatch_table **)

let binary_operator_dispatch_table m = function
| EOpPlus ->
  (make_binary_operator m (OpFloatBinary FloatPlus)) :: ((make_binary_operator
                                                           m (OpNatBinary
                                                           NatPlus)) :: [])
| EOpMinus ->
  (make_binary_operator m (OpFloatBinary FloatMinus)) :: ((make_binary_operator
                                                            m (OpNatBinary
                                                            NatMinus)) :: [])
| EOpMultiply ->
  (make_binary_operator m (OpFloatBinary FloatMult)) :: ((make_binary_operator
                                                           m (OpNatBinary
                                                           NatMult)) :: [])
| EOpDivide ->
  (make_binary_operator m (OpFloatBinary FloatDiv)) :: ((make_binary_operator
                                                          m (OpNatBinary
                                                          NatDiv)) :: [])
| EOpRemainder -> (make_binary_operator m (OpNatBinary NatRem)) :: []
| EOpGe ->
  (make_binary_operator m (OpFloatCompare FloatGe)) :: ((make_neg_binary_operator
                                                          m OpLt) :: [])
| EOpGt ->
  (make_binary_operator m (OpFloatCompare FloatGt)) :: ((make_neg_binary_operator
                                                          m OpLe) :: [])
| EOpLe ->
  (make_binary_operator m (OpFloatCompare FloatLe)) :: ((make_binary_operator
                                                          m OpLe) :: [])
| EOpLt ->
  (make_binary_operator m (OpFloatCompare FloatLt)) :: ((make_binary_operator
                                                          m OpLt) :: [])

(** val try_binary_dispatch :
    brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
    binary_dispatch_table -> ergoct_expr -> ergoct_expr -> ergoct_expr eresult **)

let rec try_binary_dispatch m nsctxt prov eop bltops eT1 eT2 =
  let t1 = exprct_type_annot m eT1 in
  let t2 = exprct_type_annot m eT2 in
  (match bltops with
   | [] ->
     efailure (ETypeError (prov,
       (ergo_format_binary_operator_dispatch_error m nsctxt eop t1 t2)))
   | b :: bltops' ->
     let (op_criteria, op_fun) = b in
     elift_both (fun r -> esuccess (op_fun prov r eT1 eT2) []) (fun _ ->
       try_binary_dispatch m nsctxt prov eop bltops' eT1 eT2)
       (op_criteria nsctxt prov t1 t2))

(** val binary_dispatch :
    brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
    ergoct_expr -> ergoct_expr -> ergoct_expr eresult **)

let binary_dispatch m nsctxt prov eop eT1 eT2 =
  try_binary_dispatch m nsctxt prov eop
    (binary_operator_dispatch_table m eop) eT1 eT2

type as_dispatch_spec =
  (namespace_ctxt -> provenance -> QLib.qcert_type -> QLib.qcert_type
  eresult) * (provenance -> QLib.qcert_type -> ergoct_expr -> ergoct_expr)

type as_dispatch_table = as_dispatch_spec list

(** val make_as_double_criteria :
    brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
    QLib.qcert_type eresult **)

let make_as_double_criteria m nsctxt prov t =
  if QLib.QcertType.qcert_type_subtype_dec m t
       (QLib.QcertType.tfloat m.brand_model_relation)
  then esuccess (QLib.QcertType.tstring m.brand_model_relation) []
  else efailure (ETypeError (prov,
         (ergo_format_as_operator_dispatch_error m nsctxt t)))

(** val make_as_double_fun :
    brand_model -> char list -> provenance -> QLib.QcertType.qtype ->
    (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr
    -> ergoct_expr **)

let make_as_double_fun m f prov t e1 =
  EBinaryBuiltin ((prov, t), (OpForeignBinary
    (Obj.magic (Coq_enhanced_binary_monetary_amount_op
      Coq_bop_monetary_amount_format))), e1, (EConst ((prov,
    (QLib.QcertType.tstring m.brand_model_relation)), (Coq_dstring f))))

(** val make_as_double : brand_model -> char list -> as_dispatch_spec **)

let make_as_double m f =
  ((make_as_double_criteria m), (make_as_double_fun m f))

(** val make_as_datetime_criteria :
    brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
    QLib.qcert_type eresult **)

let make_as_datetime_criteria m nsctxt prov t =
  if QLib.QcertType.qcert_type_subtype_dec m t
       (coq_DateTime m.brand_model_relation)
  then esuccess (QLib.QcertType.tstring m.brand_model_relation) []
  else efailure (ETypeError (prov,
         (ergo_format_as_operator_dispatch_error m nsctxt t)))

(** val make_as_datetime_fun :
    brand_model -> char list -> provenance -> QLib.QcertType.qtype ->
    (provenance * QLib.QcertType.qtype, provenance, absolute_name) ergo_expr
    -> ergoct_expr **)

let make_as_datetime_fun m f prov t e1 =
  EBinaryBuiltin ((prov, t), (OpForeignBinary
    (Obj.magic (Coq_enhanced_binary_date_time_op Coq_bop_date_time_format))),
    e1, (EUnaryBuiltin ((prov, t), (OpForeignUnary
    (Obj.magic (Coq_enhanced_unary_date_time_op
      Coq_uop_date_time_format_from_string))), (EConst ((prov,
    (QLib.QcertType.tstring m.brand_model_relation)), (Coq_dstring f))))))

(** val make_as_datetime : brand_model -> char list -> as_dispatch_spec **)

let make_as_datetime m f =
  ((make_as_datetime_criteria m), (make_as_datetime_fun m f))

(** val make_as_monetaryamount_criteria :
    brand_model -> namespace_ctxt -> provenance -> QLib.QcertType.qtype ->
    QLib.qcert_type eresult **)

let make_as_monetaryamount_criteria m nsctxt prov t =
  if QLib.QcertType.qcert_type_subtype_dec m t
       (coq_Brand enhanced_foreign_type m.brand_model_relation
         (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('m'::('o'::('n'::('e'::('y'::('.'::('M'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('A'::('m'::('o'::('u'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))) :: []))
  then esuccess (QLib.QcertType.tstring m.brand_model_relation) []
  else efailure (ETypeError (prov,
         (ergo_format_as_operator_dispatch_error m nsctxt t)))

(** val make_as_monetaryamount_fun :
    brand_model -> char list -> provenance -> QLib.qcert_type ->
    (provenance * QLib.qcert_type, provenance, absolute_name) ergo_expr ->
    ergoct_expr **)

let make_as_monetaryamount_fun m f prov t e1 =
  let doubleValue =
    make_unbrand_dot_fun m
      ('d'::('o'::('u'::('b'::('l'::('e'::('V'::('a'::('l'::('u'::('e'::[])))))))))))
      prov (QLib.QcertType.tfloat m.brand_model_relation) e1
  in
  let currencyCode = EUnaryBuiltin ((prov,
    (QLib.QcertType.tstring m.brand_model_relation)), OpToString,
    (make_unbrand_dot_fun m
      ('c'::('u'::('r'::('r'::('e'::('n'::('c'::('y'::('C'::('o'::('d'::('e'::[]))))))))))))
      prov (QLib.QcertType.tstring m.brand_model_relation) e1))
  in
  let format = EConst ((prov,
    (QLib.QcertType.tstring m.brand_model_relation)), (Coq_dstring f))
  in
  EBinaryBuiltin ((prov, t), (OpForeignBinary
  (Obj.magic (Coq_enhanced_binary_monetary_amount_op
    Coq_bop_monetary_amount_format))), doubleValue, (EBinaryBuiltin ((prov,
  (QLib.QcertType.tstring m.brand_model_relation)), (OpForeignBinary
  (Obj.magic (Coq_enhanced_binary_monetary_amount_op
    Coq_bop_monetary_code_format))), currencyCode, format)))

(** val make_as_monetaryamount :
    brand_model -> char list -> as_dispatch_spec **)

let make_as_monetaryamount m f =
  ((make_as_monetaryamount_criteria m), (make_as_monetaryamount_fun m f))

(** val as_operator_dispatch_table :
    brand_model -> char list -> as_dispatch_table **)

let as_operator_dispatch_table m f =
  (make_as_monetaryamount m f) :: ((make_as_datetime m f) :: ((make_as_double
                                                                m f) :: []))

(** val try_as_dispatch :
    brand_model -> namespace_ctxt -> provenance -> eerror -> char list ->
    as_dispatch_table -> ergoct_expr -> ergoct_expr eresult **)

let rec try_as_dispatch m nsctxt prov prev f dt eT =
  let t = exprct_type_annot m eT in
  (match dt with
   | [] -> efailure prev
   | a :: bltops' ->
     let (op_criteria, op_fun) = a in
     (match bltops' with
      | [] ->
        elift_both (fun r -> esuccess (op_fun prov r eT) []) (fun err ->
          match err with
          | ESystemError (_, _) -> efailure prev
          | _ -> efailure err) (op_criteria nsctxt prov t)
      | _ :: _ ->
        elift_both (fun r -> esuccess (op_fun prov r eT) []) (fun err ->
          try_as_dispatch m nsctxt prov err f bltops' eT)
          (op_criteria nsctxt prov t)))

(** val as_dispatch :
    brand_model -> namespace_ctxt -> provenance -> char list -> ergoct_expr
    -> ergoct_expr eresult **)

let as_dispatch m nsctxt prov f eT =
  let t = exprct_type_annot m eT in
  let init_prev = ETypeError (prov,
    (ergo_format_as_operator_dispatch_error m nsctxt t))
  in
  try_as_dispatch m nsctxt prov init_prev f (as_operator_dispatch_table m f)
    eT
