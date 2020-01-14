open Java
open NativeString

type monetary_amount_binary_op =
| Coq_bop_monetary_amount_format
| Coq_bop_monetary_code_format

val monetary_amount_binary_op_tostring :
  monetary_amount_binary_op -> char list

val cname : nstring

val monetary_amount_to_java_binary_op :
  int -> nstring -> nstring -> monetary_amount_binary_op -> java_json ->
  java_json -> java_json

type ejson_monetary_amount_runtime_op =
| EJsonRuntimeMonetaryAmountFormat
| EJsonRuntimeMonetaryCodeFormat

val ejson_monetary_amount_runtime_op_tostring :
  ejson_monetary_amount_runtime_op -> char list

val ejson_monetary_amount_runtime_op_fromstring :
  char list -> ejson_monetary_amount_runtime_op option
