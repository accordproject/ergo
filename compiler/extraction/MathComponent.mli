open Java
open NativeString

type __ = Obj.t

type math_unary_op =
| Coq_uop_math_float_of_string
| Coq_uop_math_acos
| Coq_uop_math_asin
| Coq_uop_math_atan
| Coq_uop_math_cos
| Coq_uop_math_cosh
| Coq_uop_math_sin
| Coq_uop_math_sinh
| Coq_uop_math_tan
| Coq_uop_math_tanh

val math_unary_op_tostring : math_unary_op -> char list

val math_binary_op_tostring : __ -> char list

val cname : nstring

val math_to_java_unary_op :
  int -> nstring -> nstring -> math_unary_op -> java_json -> java_json

val math_to_java_binary_op :
  int -> nstring -> nstring -> java_json -> java_json -> java_json

type ejson_math_runtime_op =
| EJsonRuntimeFloatOfString
| EJsonRuntimeAcos
| EJsonRuntimeAsin
| EJsonRuntimeAtan
| EJsonRuntimeAtan2
| EJsonRuntimeCos
| EJsonRuntimeCosh
| EJsonRuntimeSin
| EJsonRuntimeSinh
| EJsonRuntimeTan
| EJsonRuntimeTanh

val ejson_math_runtime_op_tostring : ejson_math_runtime_op -> char list

val ejson_math_runtime_op_fromstring :
  char list -> ejson_math_runtime_op option
