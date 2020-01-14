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

(** val nnrc_expr_to_imp_ejson_function :
    foreign_type -> foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2)
    foreign_to_ejson -> ('a1, 'a2) foreign_to_ejson_runtime -> brand_model ->
    char list list -> nnrc -> ('a1, 'a2) imp_ejson_function **)

let nnrc_expr_to_imp_ejson_function ft fruntime fejson ftejson frtejson bm globals fbody =
  imp_data_function_to_imp_ejson fruntime fejson ftejson
    ftejson.foreign_to_ejson_runtime frtejson (h ft bm)
    (nnrs_imp_to_imp_data_function fruntime
      (nnrs_to_nnrs_imp fruntime (nnrc_to_nnrs fruntime globals fbody)))
