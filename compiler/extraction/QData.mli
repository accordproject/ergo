open BrandRelation
open Data
open JSON
open QcertData

module QData :
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
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
