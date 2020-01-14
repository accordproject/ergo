open Datatypes
open Digits
open EmitUtil
open List0
open NativeString

type java = nstring

type java_json =
  nstring
  (* singleton inductive, whose constructor was mk_java_json *)

val from_java_json : java_json -> nstring

val mk_java_json_array : java_json list -> java_json

val mk_java_json_object : nstring -> (nstring * java_json) list -> java_json

val mk_java_json_primitive : nstring -> java_json

val mk_java_json_string : nstring -> nstring -> java_json

val java_json_NULL : java_json

val mk_java_json_nat : nstring -> int -> java_json

val mk_java_json_number : float -> java_json

val mk_java_json_bool : bool -> java_json

val mk_java_string : nstring -> nstring

val mk_java_call : nstring -> nstring -> java_json list -> java_json

val mk_java_unary_op0 : nstring -> java_json -> java_json

val mk_java_unary_op1 : nstring -> nstring -> java_json -> java_json

val mk_java_unary_opn : nstring -> nstring list -> java_json -> java_json

val mk_java_binary_op0 : nstring -> java_json -> java_json -> java_json

val mk_java_unary_op0_foreign : nstring -> nstring -> java_json -> java_json

val mk_java_binary_op0_foreign :
  nstring -> nstring -> java_json -> java_json -> java_json

val mk_java_collection : nstring -> nstring list -> nstring

val mk_java_string_collection : nstring list -> nstring
