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

(** val enhanced_to_java_data : nstring -> enhanced_data -> java_json **)

let enhanced_to_java_data _ = function
| Coq_enhanceddateTimeformat f ->
  nstring_quote
    (toString (Obj.magic date_time_format_foreign_data.foreign_data_tostring)
      f)
| Coq_enhanceddateTime f ->
  nstring_quote
    (toString (Obj.magic date_time_foreign_data.foreign_data_tostring) f)
| Coq_enhanceddateTimeduration f ->
  nstring_quote
    (toString
      (Obj.magic date_time_duration_foreign_data.foreign_data_tostring) f)
| Coq_enhanceddateTimeperiod f ->
  nstring_quote
    (toString (Obj.magic date_time_period_foreign_data.foreign_data_tostring)
      f)

(** val enhanced_to_java_unary_op :
    int -> nstring -> nstring -> enhanced_unary_op -> java_json -> java_json **)

let enhanced_to_java_unary_op indent eol quotel fu d =
  match fu with
  | Coq_enhanced_unary_uri_op op ->
    uri_to_java_unary_op indent eol quotel op d
  | Coq_enhanced_unary_log_op -> log_to_java_unary_op indent eol quotel d
  | Coq_enhanced_unary_math_op op ->
    math_to_java_unary_op indent eol quotel op d
  | Coq_enhanced_unary_date_time_op op ->
    date_time_to_java_unary_op indent eol quotel op d

(** val enhanced_to_java_binary_op :
    int -> nstring -> nstring -> enhanced_binary_op -> java_json -> java_json
    -> java_json **)

let enhanced_to_java_binary_op indent eol quotel fb d1 d2 =
  match fb with
  | Coq_enhanced_binary_math_op ->
    math_to_java_binary_op indent eol quotel d1 d2
  | Coq_enhanced_binary_date_time_op op ->
    date_time_to_java_binary_op indent eol quotel op d1 d2
  | Coq_enhanced_binary_monetary_amount_op op ->
    monetary_amount_to_java_binary_op indent eol quotel op d1 d2

(** val enhanced_foreign_to_java : foreign_to_java **)

let enhanced_foreign_to_java =
  { foreign_to_java_data = (Obj.magic enhanced_to_java_data);
    foreign_to_java_unary_op = (Obj.magic enhanced_to_java_unary_op);
    foreign_to_java_binary_op = (Obj.magic enhanced_to_java_binary_op) }
