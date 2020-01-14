open BinaryOperators
open BinaryOperatorsSem
open BrandRelation
open Data
open JSON
open QcertData
open QcertModel
open UnaryOperators
open UnaryOperatorsSem

module QOps :
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 sig
  module ErgoData :
   sig
    type json = JSON.json

    type data = Data.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : JSON.json list -> json

    val jobject : (char list * JSON.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Data.data list -> data

    val drec : (char list * Data.data) list -> data

    val dleft : data -> data

    val dright : data -> data

    val dbrand : brands -> data -> data

    val dsome : data -> data

    val dnone : data

    val dsuccess : data -> data

    val derror : data -> data
   end

  module Unary :
   sig
    type op = unary_op

    type t = op

    module Double :
     sig
      val opuminus : op

      val opabs : op

      val oplog2 : op

      val opsqrt : op

      val opsum : op

      val opnummin : op

      val opnummax : op

      val opnummean : op
     end

    val opidentity : op

    val opneg : op

    val oprec : char list -> op

    val opdot : char list -> op

    val oprecremove : char list -> op

    val oprecproject : char list list -> op

    val opbag : op

    val opsingleton : op

    val opflatten : op

    val opdistinct : op

    val opcount : op

    val optostring : op

    val opsubstring : int -> int option -> op

    val oplike : char list -> op

    val opleft : op

    val opright : op

    val opbrand : brands -> op

    val opunbrand : op

    val opcast : brands -> op

    val eval :
      brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option
   end

  module Binary :
   sig
    type op = binary_op

    type t = op

    module Double :
     sig
      val opplus : op

      val opminus : op

      val opmult : op

      val opmin : op

      val opmax : op

      val opdiv : op

      val oppow : op

      val oplt : op

      val ople : op

      val opgt : op

      val opge : op
     end

    module Integer :
     sig
      val opplusi : op

      val opminusi : op

      val opmulti : op

      val opdivi : op

      val oplti : op

      val oplei : op
     end

    module DateTime :
     sig
      val opdateadd : op

      val opdatesubtract : op

      val opdateisbefore : op

      val opdateisafter : op

      val opdatediff : op
     end

    val opequal : op

    val oprecconcat : op

    val oprecmerge : op

    val opand : op

    val opor : op

    val opbagunion : op

    val opbagdiff : op

    val opbagmin : op

    val opbagmax : op

    val opnth : op

    val opcontains : op

    val opstringconcat : op

    val opstringjoin : op

    val eval :
      brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
      ErgoData.data option
   end
 end
