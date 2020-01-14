open CoqLibAdd
open DateTimeComponent
open ForeignData
open ForeignToJava
open Java
open LogComponent
open MathComponent
open MonetaryAmountComponent
open NativeString
open QcertData
open UriComponent

val enhanced_to_java_data : nstring -> enhanced_data -> java_json

val enhanced_to_java_unary_op :
  int -> nstring -> nstring -> enhanced_unary_op -> java_json -> java_json

val enhanced_to_java_binary_op :
  int -> nstring -> nstring -> enhanced_binary_op -> java_json -> java_json
  -> java_json

val enhanced_foreign_to_java : foreign_to_java
