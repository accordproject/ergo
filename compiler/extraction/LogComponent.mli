open Java
open NativeString

type __ = Obj.t

val log_unary_op_tostring : __ -> char list

val cname : nstring

val log_to_java_unary_op : int -> nstring -> nstring -> java_json -> java_json

val ejson_log_runtime_op_tostring : __ -> char list

val ejson_log_runtime_op_fromstring : char list -> __ option
