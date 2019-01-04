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

Require Import ErgoSpec.Backend.ErgoBackend.

Require Import ErgoSpec.Common.Utils.Misc.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.NamespaceContext.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Ast.
Require Import ErgoSpec.Common.Utils.PrintTypedData.
Require Import ErgoSpec.Common.Types.ErgoCTypeUtil.
Require Import ErgoSpec.Common.Types.ErgoTypetoErgoCType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheckContext.

Section ErgoCOverloaded.
  Context {m : brand_model}.

  Import ErgoCType.

  Section UnaryOperator.
    Definition unary_dispatch_spec : Set :=
      (ergoc_type -> option ergoc_type)
      * (provenance -> ergoc_type -> ergoct_expr -> ergoct_expr).

    Definition unary_dispatch_table : Set :=
      list unary_dispatch_spec.
    
    Definition make_unary_operator_fun op prov t e : ergoct_expr :=
      EUnaryBuiltin (prov,t) op e.

    Definition make_unary_operator_criteria op t : option ergoc_type :=
      match ergoc_type_infer_unary_op op t with
      | Some (r, _) => Some r
      | None => None
      end.

    Definition make_unary_operator op : unary_dispatch_spec :=
      (make_unary_operator_criteria op, make_unary_operator_fun op).
  
    Definition make_nat_minus_fun prov t e : ergoct_expr :=
      EBinaryBuiltin (prov,t) (OpNatBinary NatMinus) (EConst (prov, tnat) (dnat 0)) e.

    Definition make_nat_minus_criteria t : option ergoc_type :=
      match ergoc_type_infer_binary_op (OpNatBinary NatMinus) tnat t with
      | Some (r, _, _) => Some r
      | None => None
      end.

    Definition make_nat_minus_operator : unary_dispatch_spec :=
      (make_nat_minus_criteria, make_nat_minus_fun).
  
    Definition unary_operator_dispatch_table (op:ergo_unary_operator) : unary_dispatch_table :=
      match op with
      | EOpUMinus =>
        (make_unary_operator (OpFloatUnary FloatNeg))
          :: (make_nat_minus_operator)
          :: nil
      | EOpDot _ =>
        nil
      end.

    Fixpoint try_unary_dispatch nsctxt prov
             (eop:ergo_unary_operator)
             (bltops:unary_dispatch_table)
             (eT:ergoct_expr) : eresult ergoct_expr :=
      let t := exprct_type_annot eT in
      match bltops with
      | nil => efailure (ETypeError prov (ergo_format_unary_operator_dispatch_error nsctxt eop t))
      | (op_criteria, op_fun) :: bltops' =>
        match op_criteria t with
        | Some r => esuccess (op_fun prov r eT) (* Found a successful dispatch *)
        | None => try_unary_dispatch nsctxt prov eop bltops' eT (* try next operator *)
        end
      end.

    Definition unary_dispatch nsctxt prov
               (eop:ergo_unary_operator)
               (eT:ergoct_expr) : eresult ergoct_expr :=
      try_unary_dispatch nsctxt prov eop (unary_operator_dispatch_table eop) eT.

  End UnaryOperator.

  Section BinaryOperator.
    Definition binary_dispatch_spec : Set :=
      ErgoOps.Binary.op * ((provenance * ergoc_type) -> ergoct_expr -> ergoct_expr -> ergoct_expr).

    Definition binary_dispatch_table : Set :=
      list binary_dispatch_spec.
    
    Definition make_binary_operator_fun op a e1 e2 : ergoct_expr :=
      EBinaryBuiltin a op e1 e2.

    Definition make_binary_operator op : binary_dispatch_spec :=
      (op, make_binary_operator_fun op).
  
    Definition make_neg_binary_operator_fun op a e1 e2 : ergoct_expr :=
      EUnaryBuiltin a OpNeg (EBinaryBuiltin a op e1 e2).

    Definition make_neg_binary_operator op : binary_dispatch_spec :=
      (op, make_neg_binary_operator_fun op).

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
      | (op, op_fun) :: bltops' =>
        match ergoc_type_infer_binary_op op t1 t2 with
        | Some (r, _, _) => esuccess (op_fun (prov,r) eT1 eT2) (* Found a successful dispatch *)
        | None => try_binary_dispatch nsctxt prov eop bltops' eT1 eT2 (* try next operator *)
        end
      end.

    Definition binary_dispatch nsctxt prov
               (eop:ergo_binary_operator)
               (eT1 eT2:ergoct_expr) : eresult ergoct_expr :=
      try_binary_dispatch nsctxt prov eop (binary_operator_dispatch_table eop) eT1 eT2.

  End BinaryOperator.
End ErgoCOverloaded.
