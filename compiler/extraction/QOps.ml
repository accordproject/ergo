open BinaryOperators
open BinaryOperatorsSem
open BrandRelation
open Data
open JSON
open QcertData
open QcertModel
open UnaryOperators
open UnaryOperatorsSem

module QOps =
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 struct
  module ErgoData = QData.QData(Coq_ergomodel)

  module Unary =
   struct
    type op = unary_op

    type t = op

    module Double =
     struct
      (** val opuminus : op **)

      let opuminus =
        OpFloatUnary FloatNeg

      (** val opabs : op **)

      let opabs =
        OpFloatUnary FloatAbs

      (** val oplog2 : op **)

      let oplog2 =
        OpFloatUnary FloatLog

      (** val opsqrt : op **)

      let opsqrt =
        OpFloatUnary FloatSqrt

      (** val opsum : op **)

      let opsum =
        OpFloatSum

      (** val opnummin : op **)

      let opnummin =
        OpFloatBagMin

      (** val opnummax : op **)

      let opnummax =
        OpFloatBagMax

      (** val opnummean : op **)

      let opnummean =
        OpFloatMean
     end

    (** val opidentity : op **)

    let opidentity =
      OpIdentity

    (** val opneg : op **)

    let opneg =
      OpNeg

    (** val oprec : char list -> op **)

    let oprec x =
      OpRec x

    (** val opdot : char list -> op **)

    let opdot x =
      OpDot x

    (** val oprecremove : char list -> op **)

    let oprecremove x =
      OpRecRemove x

    (** val oprecproject : char list list -> op **)

    let oprecproject x =
      OpRecProject x

    (** val opbag : op **)

    let opbag =
      OpBag

    (** val opsingleton : op **)

    let opsingleton =
      OpSingleton

    (** val opflatten : op **)

    let opflatten =
      OpFlatten

    (** val opdistinct : op **)

    let opdistinct =
      OpDistinct

    (** val opcount : op **)

    let opcount =
      OpCount

    (** val optostring : op **)

    let optostring =
      OpToString

    (** val opsubstring : int -> int option -> op **)

    let opsubstring x x0 =
      OpSubstring (x, x0)

    (** val oplike : char list -> op **)

    let oplike x =
      OpLike x

    (** val opleft : op **)

    let opleft =
      OpLeft

    (** val opright : op **)

    let opright =
      OpRight

    (** val opbrand : brands -> op **)

    let opbrand b =
      OpBrand b

    (** val opunbrand : op **)

    let opunbrand =
      OpUnbrand

    (** val opcast : brands -> op **)

    let opcast x =
      OpCast x

    (** val eval :
        brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option **)

    let eval h uop d =
      unary_op_eval enhanced_foreign_data h enhanced_foreign_operators uop d
   end

  module Binary =
   struct
    type op = binary_op

    type t = op

    module Double =
     struct
      (** val opplus : op **)

      let opplus =
        OpFloatBinary FloatPlus

      (** val opminus : op **)

      let opminus =
        OpFloatBinary FloatMinus

      (** val opmult : op **)

      let opmult =
        OpFloatBinary FloatMult

      (** val opmin : op **)

      let opmin =
        OpFloatBinary FloatMin

      (** val opmax : op **)

      let opmax =
        OpFloatBinary FloatMax

      (** val opdiv : op **)

      let opdiv =
        OpFloatBinary FloatDiv

      (** val oppow : op **)

      let oppow =
        OpFloatBinary FloatPow

      (** val oplt : op **)

      let oplt =
        OpFloatCompare FloatLt

      (** val ople : op **)

      let ople =
        OpFloatCompare FloatLe

      (** val opgt : op **)

      let opgt =
        OpFloatCompare FloatGt

      (** val opge : op **)

      let opge =
        OpFloatCompare FloatGe
     end

    module Integer =
     struct
      (** val opplusi : op **)

      let opplusi =
        OpNatBinary NatPlus

      (** val opminusi : op **)

      let opminusi =
        OpNatBinary NatMinus

      (** val opmulti : op **)

      let opmulti =
        OpNatBinary NatMult

      (** val opdivi : op **)

      let opdivi =
        OpNatBinary NatDiv

      (** val oplti : op **)

      let oplti =
        OpLt

      (** val oplei : op **)

      let oplei =
        OpLe
     end

    module DateTime =
     struct
      (** val opdateadd : op **)

      let opdateadd =
        CompEnhanced.Enhanced.Ops.Binary.coq_OpDateTimeAdd

      (** val opdatesubtract : op **)

      let opdatesubtract =
        CompEnhanced.Enhanced.Ops.Binary.coq_OpDateTimeSubtract

      (** val opdateisbefore : op **)

      let opdateisbefore =
        CompEnhanced.Enhanced.Ops.Binary.coq_OpDateTimeIsBefore

      (** val opdateisafter : op **)

      let opdateisafter =
        CompEnhanced.Enhanced.Ops.Binary.coq_OpDateTimeIsAfter

      (** val opdatediff : op **)

      let opdatediff =
        CompEnhanced.Enhanced.Ops.Binary.coq_OpDateTimeDiff
     end

    (** val opequal : op **)

    let opequal =
      OpEqual

    (** val oprecconcat : op **)

    let oprecconcat =
      OpRecConcat

    (** val oprecmerge : op **)

    let oprecmerge =
      OpRecMerge

    (** val opand : op **)

    let opand =
      OpAnd

    (** val opor : op **)

    let opor =
      OpOr

    (** val opbagunion : op **)

    let opbagunion =
      OpBagUnion

    (** val opbagdiff : op **)

    let opbagdiff =
      OpBagDiff

    (** val opbagmin : op **)

    let opbagmin =
      OpBagMin

    (** val opbagmax : op **)

    let opbagmax =
      OpBagMax

    (** val opnth : op **)

    let opnth =
      OpBagNth

    (** val opcontains : op **)

    let opcontains =
      OpContains

    (** val opstringconcat : op **)

    let opstringconcat =
      OpStringConcat

    (** val opstringjoin : op **)

    let opstringjoin =
      OpStringJoin

    (** val eval :
        brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
        ErgoData.data option **)

    let eval h bop d1 d2 =
      binary_op_eval h enhanced_foreign_data enhanced_foreign_operators bop
        d1 d2
   end
 end
