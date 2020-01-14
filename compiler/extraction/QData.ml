open BrandRelation
open Data
open JSON
open QcertData

module QData =
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 struct
  type json = JSON.json

  type data = Data.data

  type t = data

  (** val jnull : json **)

  let jnull =
    Coq_jnull

  (** val jnumber : float -> json **)

  let jnumber z =
    Coq_jnumber z

  (** val jbool : bool -> json **)

  let jbool b =
    Coq_jbool b

  (** val jstring : char list -> json **)

  let jstring s =
    Coq_jstring s

  (** val jarray : JSON.json list -> json **)

  let jarray jl =
    Coq_jarray jl

  (** val jobject : (char list * JSON.json) list -> json **)

  let jobject jl =
    Coq_jobject jl

  (** val dunit : data **)

  let dunit =
    Coq_dunit

  (** val dnat : int -> data **)

  let dnat z =
    Coq_dnat z

  (** val dfloat : float -> data **)

  let dfloat f =
    Coq_dfloat f

  (** val dbool : bool -> data **)

  let dbool b =
    Coq_dbool b

  (** val dstring : char list -> data **)

  let dstring s =
    Coq_dstring s

  (** val dcoll : Data.data list -> data **)

  let dcoll dl =
    Coq_dcoll dl

  (** val drec : (char list * Data.data) list -> data **)

  let drec dl =
    Coq_drec dl

  (** val dleft : data -> data **)

  let dleft x =
    Coq_dleft x

  (** val dright : data -> data **)

  let dright x =
    Coq_dright x

  (** val dbrand : brands -> data -> data **)

  let dbrand b x =
    Coq_dbrand (b, x)

  (** val dsome : data -> data **)

  let dsome =
    dsome enhanced_foreign_data

  (** val dnone : data **)

  let dnone =
    dnone enhanced_foreign_data

  (** val dsuccess : data -> data **)

  let dsuccess x =
    Coq_dleft x

  (** val derror : data -> data **)

  let derror x =
    Coq_dright x
 end
