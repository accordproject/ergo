(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Common.PrintTypedData.
Require Import ErgoSpec.Types.ErgoCTypeUtil.
Require Import ErgoSpec.Types.ErgoTypetoErgoCType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheckContext.

Section ErgoCOverloaded.
  Context {m : brand_model}.

  Import QcertType.

  Section UnaryOperator.
    Definition unary_dispatch_spec : Set :=
      (namespace_ctxt -> provenance -> ergoc_type -> eresult ergoc_type)
      * (provenance -> ergoc_type -> ergoct_expr -> ergoct_expr).

    Definition unary_dispatch_table : Set :=
      list unary_dispatch_spec.
    
    Definition make_unary_operator_fun op prov t e : ergoct_expr :=
      EUnaryBuiltin (prov,t) op e.

    Definition make_unary_operator op : unary_dispatch_spec :=
      (make_unary_operator_criteria op, make_unary_operator_fun op).
  
    Definition make_nat_minus_fun prov t e : ergoct_expr :=
      EBinaryBuiltin (prov,t) (OpNatBinary NatMinus) (EConst (prov, tnat) (dnat 0)) e.

    Definition make_nat_minus_criteria nsctxt prov t : eresult ergoc_type :=
      match ergoc_type_infer_binary_op (OpNatBinary NatMinus) tnat t with
      | Some (r, _, _) => esuccess r nil
      | None => efailure (ETypeError prov (ergo_format_binop_error nsctxt (OpNatBinary NatMinus) tnat t))
      end.

    Definition make_nat_minus_operator : unary_dispatch_spec :=
      (make_nat_minus_criteria, make_nat_minus_fun).

    Definition make_dot_criteria name nsctxt prov t : eresult ergoc_type :=
      match ergoc_type_infer_unary_op (OpDot name) t with
      | Some (r, _) => esuccess r nil
      | None => efailure (ETypeError prov (ergo_format_unop_error nsctxt (OpDot name) t))
      end.

    Definition make_dot_operator name : unary_dispatch_spec :=
      (make_dot_criteria name, make_unary_operator_fun (OpDot name)).

    Definition make_unbrand_dot_fun name prov t e : ergoct_expr :=
      EUnaryBuiltin (prov,t) (OpDot name) (EUnaryBuiltin (prov,t) OpUnbrand e).

    Definition make_unbrand_dot_criteria name nsctxt prov t : eresult ergoc_type :=
      match ergoc_type_infer_unary_op OpUnbrand t with
      | Some (r1, _) =>
        match ergoc_type_infer_unary_op (OpDot name) r1 with
        | Some (r2, _) => esuccess r2 nil
        | None => efailure (ETypeError prov (ergo_format_unop_error nsctxt (OpDot name) t))
        end
      | None => efailure (ESystemError prov "WRONG KIND")
      end.

    Definition make_unbrand_dot_operator name : unary_dispatch_spec :=
      (make_unbrand_dot_criteria name, make_unbrand_dot_fun name).

    Definition unary_operator_dispatch_table (op:ergo_unary_operator) : unary_dispatch_table :=
      match op with
      | EOpUMinus =>
        (make_unary_operator (OpFloatUnary FloatNeg))
          :: (make_nat_minus_operator)
          :: nil
      | EOpDot name =>
         (make_unbrand_dot_operator name)
          :: (make_dot_operator name)
          :: nil
      end.

    Fixpoint try_unary_dispatch
             nsctxt prov
             (prev: eerror)
             (eop:ergo_unary_operator)
             (bltops:unary_dispatch_table)
             (eT:ergoct_expr) : eresult ergoct_expr :=
      let t := exprct_type_annot eT in
      match bltops with
      | nil => efailure (ETypeError prov (ergo_format_unary_operator_dispatch_error nsctxt eop t))
      | (op_criteria, op_fun) :: nil =>
        elift_both
          (fun r => esuccess (op_fun prov r eT) nil)               (* found a successful dispatch *)
          (fun err =>
             match err with
             | ESystemError _ _ => efailure prev (* Fall back to previous good error *)
             | _ => efailure err
             end)
          (op_criteria nsctxt prov t)
      | (op_criteria, op_fun) :: bltops' =>
        elift_both
          (fun r => esuccess (op_fun prov r eT) nil)               (* found a successful dispatch *)
          (fun err => try_unary_dispatch nsctxt prov err eop bltops' eT) (* try next operator *)
          (op_criteria nsctxt prov t)
      end.

    Definition unary_dispatch nsctxt prov
               (eop:ergo_unary_operator)
               (eT:ergoct_expr) : eresult ergoct_expr :=
      let t := exprct_type_annot eT in
      let init_prev := ETypeError prov (ergo_format_unary_operator_dispatch_error nsctxt eop t) in
      try_unary_dispatch nsctxt prov init_prev eop (unary_operator_dispatch_table eop) eT.

  End UnaryOperator.

  Section BinaryOperator.
    Definition binary_dispatch_spec : Set :=
      (namespace_ctxt -> provenance -> ergoc_type -> ergoc_type -> eresult ergoc_type)
      * (provenance -> ergoc_type -> ergoct_expr -> ergoct_expr -> ergoct_expr).

    Definition binary_dispatch_table : Set :=
      list binary_dispatch_spec.

    Definition make_binary_operator_fun op prov t e1 e2 : ergoct_expr :=
      EBinaryBuiltin (prov,t) op e1 e2.

    Definition make_binary_operator op : binary_dispatch_spec :=
      (make_binary_operator_criteria op, make_binary_operator_fun op).
  
    Definition make_neg_binary_operator_fun op prov t e1 e2 : ergoct_expr :=
      EUnaryBuiltin (prov,t) OpNeg (EBinaryBuiltin (prov,t) op e1 e2).

    Definition make_neg_binary_operator op : binary_dispatch_spec :=
      (make_binary_operator_criteria op, make_neg_binary_operator_fun op).

    Definition binary_operator_dispatch_table (op:ergo_binary_operator) : binary_dispatch_table :=
      match op with
      | EOpPlus =>
        (make_binary_operator (OpFloatBinary FloatPlus))
          :: (make_binary_operator (OpNatBinary NatPlus))
          :: nil
      | EOpMinus =>
        (make_binary_operator (OpFloatBinary FloatMinus))
          :: (make_binary_operator (OpNatBinary NatMinus))
          :: nil
      | EOpMultiply =>
        (make_binary_operator (OpFloatBinary FloatMult))
          :: (make_binary_operator (OpNatBinary NatMult))
          :: nil
      | EOpDivide =>
        (make_binary_operator (OpFloatBinary FloatDiv))
          :: (make_binary_operator (OpNatBinary NatDiv))
          :: nil
      | EOpRemainder =>
        (make_binary_operator (OpNatBinary NatRem))
          :: nil
      | EOpGe =>
        (make_binary_operator (OpFloatCompare FloatGe))
          :: (make_neg_binary_operator OpLt)
          :: nil
      | EOpGt =>
        (make_binary_operator (OpFloatCompare FloatGt))
          :: (make_neg_binary_operator OpLe) :: nil
      | EOpLe =>
        (make_binary_operator (OpFloatCompare FloatLe))
          :: (make_binary_operator OpLe)
          :: nil
      | EOpLt =>
        (make_binary_operator (OpFloatCompare FloatLt))
          :: (make_binary_operator OpLt)
          :: nil
      end.

    Fixpoint try_binary_dispatch nsctxt prov
             (eop:ergo_binary_operator)
             (bltops:binary_dispatch_table)
             (eT1 eT2:ergoct_expr) : eresult ergoct_expr :=
      let t1 := exprct_type_annot eT1 in
      let t2 := exprct_type_annot eT2 in
      match bltops with
      | nil => efailure (ETypeError prov (ergo_format_binary_operator_dispatch_error nsctxt eop t1 t2))
      | (op_criteria, op_fun) :: bltops' =>
        elift_both
          (fun r => esuccess (op_fun prov r eT1 eT2) nil) (* Found a successful dispatch *)
          (fun _ => try_binary_dispatch nsctxt prov eop bltops' eT1 eT2) (* try next operator *)
          (op_criteria nsctxt prov t1 t2)
      end.

    Definition binary_dispatch nsctxt prov
               (eop:ergo_binary_operator)
               (eT1 eT2:ergoct_expr) : eresult ergoct_expr :=
      try_binary_dispatch nsctxt prov eop (binary_operator_dispatch_table eop) eT1 eT2.

  End BinaryOperator.

  Section AsExpr.
    Definition as_dispatch_spec : Set :=
      (namespace_ctxt -> provenance -> ergoc_type -> eresult ergoc_type)
      * (provenance -> ergoc_type -> ergoct_expr -> ergoct_expr).

    Definition as_dispatch_table : Set :=
      list as_dispatch_spec.

    Definition make_as_double_criteria nsctxt prov t : eresult ergoc_type :=
      if (ergoc_type_subtype_dec t tfloat)
      then esuccess tstring nil
      else efailure (ETypeError prov (ergo_format_as_operator_dispatch_error nsctxt t)).

    Definition make_as_double_fun f prov t e1 : ergoct_expr :=
      EBinaryBuiltin (prov,t) (OpForeignBinary (enhanced_binary_monetary_amount_op bop_monetary_amount_format)) e1 (EConst (prov,tstring) (dstring f)).

    Definition make_as_double f : as_dispatch_spec :=
      (make_as_double_criteria, make_as_double_fun f).

    Definition make_as_datetime_criteria nsctxt prov t : eresult ergoc_type :=
      if (ergoc_type_subtype_dec t DateTime)
      then esuccess tstring nil
      else efailure (ETypeError prov (ergo_format_as_operator_dispatch_error nsctxt t)).

    Definition make_as_datetime_fun f prov t e1 : ergoct_expr :=
      EBinaryBuiltin (prov,t) (OpForeignBinary (enhanced_binary_date_time_op bop_date_time_format)) e1
                     (EUnaryBuiltin (prov,t) (OpForeignUnary (enhanced_unary_date_time_op uop_date_time_format_from_string)) (EConst (prov,tstring) (dstring f))).

    Definition make_as_datetime f : as_dispatch_spec :=
      (make_as_datetime_criteria, make_as_datetime_fun f).

    Definition make_as_monetaryamount_criteria nsctxt prov t : eresult ergoc_type :=
      if (ergoc_type_subtype_dec t (Brand ("org.accordproject.money.MonetaryAmount"%string::nil)))
      then esuccess tstring nil
      else efailure (ETypeError prov (ergo_format_as_operator_dispatch_error nsctxt t)).

    Definition make_as_monetaryamount_fun f prov t e1 : ergoct_expr :=
      let doubleValue := make_unbrand_dot_fun "doubleValue" prov tfloat e1 in
      let currencyCode := EUnaryBuiltin (prov,tstring) OpToString (make_unbrand_dot_fun "currencyCode" prov tstring e1) in
      let format := EConst (prov,tstring) (dstring f) in
      EBinaryBuiltin (prov,t) (OpForeignBinary (enhanced_binary_monetary_amount_op bop_monetary_amount_format))
                     doubleValue
                     (EBinaryBuiltin (prov,tstring) (OpForeignBinary (enhanced_binary_monetary_amount_op bop_monetary_code_format))
                                     currencyCode
                                     format).

    Definition make_as_monetaryamount f : as_dispatch_spec :=
      (make_as_monetaryamount_criteria, make_as_monetaryamount_fun f).

    Definition as_operator_dispatch_table f : as_dispatch_table :=
      (make_as_monetaryamount f)
        :: (make_as_datetime f)
        :: (make_as_double f)
        :: nil.

    Fixpoint try_as_dispatch
             nsctxt prov
             (prev: eerror)
             (f:string)
             (dt:as_dispatch_table)
             (eT:ergoct_expr) : eresult ergoct_expr :=
      let t := exprct_type_annot eT in
      match dt with
      | nil => efailure prev
      | (op_criteria, op_fun) :: nil =>
        elift_both
          (fun r => esuccess (op_fun prov r eT) nil)               (* found a successful dispatch *)
          (fun err =>
             match err with
             | ESystemError _ _ => efailure prev (* Fall back to previous good error *)
             | _ => efailure err
             end)
          (op_criteria nsctxt prov t)
      | (op_criteria, op_fun) :: bltops' =>
        elift_both
          (fun r => esuccess (op_fun prov r eT) nil)                  (* found a successful dispatch *)
          (fun err => try_as_dispatch nsctxt prov err f bltops' eT) (* try next type *)
          (op_criteria nsctxt prov t)
      end.

    Definition as_dispatch nsctxt prov f
               (eT:ergoct_expr) : eresult ergoct_expr :=
      let t := exprct_type_annot eT in
      let init_prev := ETypeError prov (ergo_format_as_operator_dispatch_error nsctxt t) in
      try_as_dispatch nsctxt prov init_prev f (as_operator_dispatch_table f) eT.
   
  End AsExpr.

End ErgoCOverloaded.
