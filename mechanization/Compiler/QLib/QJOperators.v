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
Require Import Jura.Compiler.Model.JuraRuntime.
Require Import Jura.Compiler.Model.JuraModel.

Module QJOperators(juramodel:JuraCompilerModel).
  
  Module Unary.

    Definition op : Set  
      := UnaryOperators.unary_op.
    Definition t : Set 
      := op.

    Module ZArith.
      Definition opabs : op 
        := UnaryOperators.OpArithUnary UnaryOperators.ArithAbs.
      Definition oplog2 : op 
        := UnaryOperators.OpArithUnary UnaryOperators.ArithLog2.
      Definition opsqrt : op 
        := UnaryOperators.OpArithUnary UnaryOperators.ArithSqrt.
    End ZArith.

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
    Definition opsum : op 
      := UnaryOperators.OpSum.
    Definition opnummin : op 
      := UnaryOperators.OpNumMin.
    Definition opnummax : op 
      := UnaryOperators.OpNumMax.
    Definition opnummean : op 
      := UnaryOperators.OpNumMean.
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

  (* Note that foreign operators should be encapuslated and 
     exported as part of the model *)
  End Unary.

  Module Binary.

    Definition op : Set 
      := BinaryOperators.binary_op.
    Definition t : Set 
      := op.

    Module ZArith.
      Definition opplus : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithPlus.
      Definition opminus : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithMinus.
      Definition opmult : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithMult.
      Definition opmin : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithMin.
      Definition opmax : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithMax.
      Definition opdiv : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithDivide.
      Definition oprem : op 
        := BinaryOperators.OpArithBinary BinaryOperators.ArithRem.
    End ZArith.
    
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

    (* Note that foreign operators should be encapuslated and 
       exported as part of the model *)
  End Binary.
End QJOperators.

