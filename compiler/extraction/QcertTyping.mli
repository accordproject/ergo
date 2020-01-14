open BrandRelation
open DateTimeComponent
open ForeignOperatorsTyping
open ForeignTyping
open MathComponent
open MonetaryAmountComponent
open QcertData
open QcertDataTyping
open QcertType
open RSubtype
open RType
open TBrandModel
open UriComponent

val coq_DateTimeFormat : brand_relation -> rtype

val coq_DateTime : brand_relation -> rtype

val coq_DateTimeDuration : brand_relation -> rtype

val coq_DateTimePeriod : brand_relation -> rtype

val isDateTimeFormat : brand_model -> rtype -> bool

val isDateTime : brand_model -> rtype -> bool

val isDateTimeDuration : brand_model -> rtype -> bool

val isDateTimePeriod : brand_model -> rtype -> bool

val isNat : brand_model -> rtype -> bool

val isString : brand_model -> rtype -> bool

val isFloat : brand_model -> rtype -> bool

val tuncoll : brand_model -> rtype -> rtype option

val uri_unary_op_type_infer :
  brand_model -> uri_unary_op -> rtype -> rtype option

val log_unary_op_type_infer : brand_model -> rtype -> rtype option

val math_unary_op_type_infer :
  brand_model -> math_unary_op -> rtype -> rtype option

val date_time_unary_op_type_infer :
  brand_model -> date_time_unary_op -> rtype -> rtype option

val uri_unary_op_type_infer_sub :
  brand_model -> uri_unary_op -> rtype -> (rtype * rtype) option

val log_unary_op_type_infer_sub :
  brand_model -> rtype -> (rtype * rtype) option

val math_unary_op_type_infer_sub :
  brand_model -> math_unary_op -> rtype -> (rtype * rtype) option

val date_time_unary_op_type_infer_sub :
  brand_model -> date_time_unary_op -> rtype -> (rtype * rtype) option

val enhanced_unary_op_typing_infer :
  brand_model -> enhanced_unary_op -> rtype -> rtype option

val enhanced_unary_op_typing_infer_sub :
  brand_model -> enhanced_unary_op -> rtype -> (rtype * rtype) option

val math_binary_op_type_infer : brand_model -> rtype -> rtype -> rtype option

val date_time_binary_op_type_infer :
  brand_model -> date_time_binary_op -> rtype -> rtype -> rtype option

val monetary_amount_binary_op_type_infer :
  brand_model -> monetary_amount_binary_op -> rtype -> rtype -> rtype option

val math_binary_op_type_infer_sub :
  brand_model -> rtype -> rtype -> ((rtype * rtype) * rtype) option

val date_time_binary_op_type_infer_sub :
  brand_model -> date_time_binary_op -> rtype -> rtype ->
  ((rtype * rtype) * rtype) option

val monetary_amount_binary_op_type_infer_sub :
  brand_model -> monetary_amount_binary_op -> rtype -> rtype ->
  ((rtype * rtype) * rtype) option

val enhanced_binary_op_typing_infer :
  brand_model -> enhanced_binary_op -> rtype -> rtype -> rtype option

val enhanced_binary_op_typing_infer_sub :
  brand_model -> enhanced_binary_op -> rtype -> rtype ->
  ((rtype * rtype) * rtype) option

val enhanced_foreign_operators_typing :
  brand_model -> foreign_operators_typing

val enhanced_foreign_typing : brand_model -> foreign_typing
