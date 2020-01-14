open CompDriver
open CompEval
open CompLang
open ForeignDataToEJson
open ForeignEJson
open ForeignRuntime
open ForeignToEJsonRuntime
open ForeignType
open ImpDatatoImpEJson
open ImpEJson
open NNRSimptoImpData
open TBrandModel

val nnrc_expr_to_imp_ejson_function :
  foreign_type -> foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2)
  foreign_to_ejson -> ('a1, 'a2) foreign_to_ejson_runtime -> brand_model ->
  char list list -> nnrc -> ('a1, 'a2) imp_ejson_function
