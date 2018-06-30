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

Require Import Ascii.
Require Import ZArith.
Require Qcert.Common.Brands.BrandRelation.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.
Require Import ErgoSpec.Backend.Lib.EData.

Module EOperators(ergomodel:ErgoBackendModel).
  Module ErgoData := EData.EData ergomodel.
  
  Module Unary.
    Definition op : Set  
      := UnaryOperators.unary_op.
    Definition t : Set 
      := op.

    Module Double.
      Definition opuminus : op 
        := UnaryOperators.OpFloatUnary UnaryOperators.FloatNeg.
      Definition opabs : op 
        := UnaryOperators.OpFloatUnary UnaryOperators.FloatAbs.
      Definition oplog2 : op 
        := UnaryOperators.OpFloatUnary UnaryOperators.FloatLog.
      Definition opsqrt : op 
        := UnaryOperators.OpFloatUnary UnaryOperators.FloatSqrt.
      Definition opsum : op 
        := UnaryOperators.OpFloatSum.
      Definition opnummin : op 
        := UnaryOperators.OpFloatBagMin.
      Definition opnummax : op 
        := UnaryOperators.OpFloatBagMax.
      Definition opnummean : op 
        := UnaryOperators.OpFloatMean.
    End Double.

    Definition opidentity : op 
      := UnaryOperators.OpIdentity.
    Definition opneg : op 
      := UnaryOperators.OpNeg.
    Definition oprec : String.string -> op 
      := UnaryOperators.OpRec.
    Definition opdot : String.string -> op 
      := UnaryOperators.OpDot.
    Definition oprecremove : String.string -> op 
      := UnaryOperators.OpRecRemove.
    Definition oprecproject : list String.string -> op 
      := UnaryOperators.OpRecProject.
    Definition opbag : op 
      := UnaryOperators.OpBag.
    Definition opsingleton : op 
      := UnaryOperators.OpSingleton.
    Definition opflatten : op 
      := UnaryOperators.OpFlatten.
    Definition opdistinct : op 
      := UnaryOperators.OpDistinct.
    Definition opcount : op 
      := UnaryOperators.OpCount.
    Definition optostring : op 
      := UnaryOperators.OpToString.
    Definition opsubstring : Z -> option Z -> op 
      := UnaryOperators.OpSubstring.
    Definition oplike : String.string -> option Ascii.ascii -> op 
      := UnaryOperators.OpLike.
    Definition opleft : op 
      := UnaryOperators.OpLeft.
    Definition opright : op 
      := UnaryOperators.OpRight.
    Definition opbrand b : op 
      := UnaryOperators.OpBrand b.
    Definition opunbrand : op 
      := UnaryOperators.OpUnbrand.
    Definition opcast : BrandRelation.brands -> op 
      := UnaryOperators.OpCast.

    Definition eval
               (h:BrandRelation.brand_relation_t)
               (uop:UnaryOperators.unary_op)
               (d:ErgoData.data) : option ErgoData.data
      := UnaryOperatorsSem.unary_op_eval h uop d.

  (* Note that foreign operators should be encapuslated and 
     exported as part of the model *)
  End Unary.

  Module Binary.

    Definition op : Set 
      := BinaryOperators.binary_op.
    Definition t : Set 
      := op.

    Module Double.
      Definition opplus : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatPlus.
      Definition opminus : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMinus.
      Definition opmult : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMult.
      Definition opmin : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMin.
      Definition opmax : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatMax.
      Definition opdiv : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatDiv.
      Definition oppow : op 
        := BinaryOperators.OpFloatBinary BinaryOperators.FloatPow.
    End Double.

    Module Integer.
      Definition opplusi : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatPlus.
      Definition opminusi : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMinus.
      Definition opmulti : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatMult.
      Definition opdivi : op 
        := BinaryOperators.OpNatBinary BinaryOperators.NatDiv.
    End Integer.

    Module DateTime.
      Definition opdateplus : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimePlus.
      Definition opdateminus : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeMinus.
      Definition opdatene : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeNe.
      Definition opdatelt : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeLt.
      Definition opdatele : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeLe.
      Definition opdategt : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeGt.
      Definition opdatege : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeGe.
      Definition opdateintervaldays : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeIntervalDays.
      Definition opdateintervalseconds : op
        := ErgoEnhancedModel.CompEnhanced.Enhanced.Ops.Binary.OpDateTimeIntervalSeconds.
    End DateTime.

    Definition opequal : op
      := BinaryOperators.OpEqual.
    Definition oprecconcat : op
      := BinaryOperators.OpRecConcat.
    Definition oprecmerge : op
      := BinaryOperators.OpRecMerge.
    Definition opand : op
      := BinaryOperators.OpAnd.
    Definition opor : op
      := BinaryOperators.OpOr.
    Definition oplt : op
      := BinaryOperators.OpLt.
    Definition ople : op
      := BinaryOperators.OpLe.
    Definition opbagunion : op
      := BinaryOperators.OpBagUnion.
    Definition opbagdiff : op
      := BinaryOperators.OpBagDiff.
    Definition opbagmin : op
      := BinaryOperators.OpBagMin.
    Definition opbagmax : op
      := BinaryOperators.OpBagMax.
    Definition opcontains : op
      := BinaryOperators.OpContains.
    Definition opstringconcat : op
      := BinaryOperators.OpStringConcat.

    Definition eval
               (h:BrandRelation.brand_relation_t)
               (bop:BinaryOperators.binary_op)
               (d1 d2:ErgoData.data) : option ErgoData.data
      := BinaryOperatorsSem.binary_op_eval h bop d1 d2.

  (* Note that foreign operators should be encapuslated and 
       exported as part of the model *)
  End Binary.
End EOperators.

