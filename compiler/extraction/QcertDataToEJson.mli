open DateTimeComponent
open ForeignData
open ForeignDataToEJson
open ForeignOperators
open ForeignToEJsonRuntime
open MathComponent
open MonetaryAmountComponent
open QcertData
open QcertEJson
open UriComponent

val enhanced_foreign_to_ejson_obligation_1 :
  enhanced_ejson -> foreign_data_model

val enhanced_foreign_to_ejson_obligation_2 :
  foreign_data_model -> enhanced_ejson

val enhanced_foreign_to_ejson :
  (enhanced_ejson, enhanced_foreign_ejson_runtime_op) foreign_to_ejson

val unary_op_to_ejson : enhanced_unary_op -> enhanced_foreign_ejson_runtime_op

val binary_op_to_ejson :
  enhanced_binary_op -> enhanced_foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime_obligation_1 :
  foreign_operators_unary -> enhanced_foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime_obligation_3 :
  foreign_operators_binary -> enhanced_foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime :
  (enhanced_ejson, enhanced_foreign_ejson_runtime_op) foreign_to_ejson_runtime
