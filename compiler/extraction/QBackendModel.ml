open ForeignData
open ForeignType
open QcertEJson

module type QBackendModel =
 sig
  type ergo_foreign_ejson = enhanced_ejson

  type ergo_foreign_ejson_runtime_op = enhanced_foreign_ejson_runtime_op

  val ergo_foreign_data : foreign_data

  val ergo_foreign_type : foreign_type
 end
