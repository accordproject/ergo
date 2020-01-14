open Java
open NativeString

type uri_unary_op =
| Coq_uop_uri_encode
| Coq_uop_uri_decode

val uri_unary_op_tostring : uri_unary_op -> char list

val cname : nstring

val uri_to_java_unary_op :
  int -> nstring -> nstring -> uri_unary_op -> java_json -> java_json

type ejson_uri_runtime_op =
| EJsonRuntimeUriEncode
| EJsonRuntimeUriDecode

val ejson_uri_runtime_op_tostring : ejson_uri_runtime_op -> char list

val ejson_uri_runtime_op_fromstring : char list -> ejson_uri_runtime_op option
