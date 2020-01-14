open BrandRelation
open CompLang
open Dataframe
open ForeignDataToEJson
open ForeignEJson
open ForeignRuntime
open ForeignToEJsonRuntime
open ForeignType
open ImpDatatoImpEJson
open JavaScriptAsttoJavaScript
open NNRCtoNNRS
open NNRSimptoImpData
open NNRStoNNRSimp
open TBrandModel

(** val nnrc_to_nnrs : foreign_runtime -> var list -> nnrc -> nnrs **)

let nnrc_to_nnrs =
  nnrc_to_nnrs_top

(** val nnrs_to_nnrs_imp : foreign_runtime -> nnrs -> nnrs_imp **)

let nnrs_to_nnrs_imp fruntime q =
  nnrs_to_nnrs_imp_top fruntime ('$'::[]) q

(** val nnrs_imp_to_imp_data :
    foreign_runtime -> char list -> nnrs_imp -> imp_data **)

let nnrs_imp_to_imp_data =
  nnrs_imp_to_imp_data_top

(** val imp_data_to_imp_ejson :
    foreign_type -> foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2)
    foreign_to_ejson -> ('a1, 'a2) foreign_to_ejson_runtime -> brand_model ->
    imp_data -> ('a1, 'a2) imp_ejson **)

let imp_data_to_imp_ejson _ fruntime fejson ftejson frtejson bm q =
  imp_data_to_imp_ejson fruntime fejson ftejson
    ftejson.foreign_to_ejson_runtime frtejson
    (brand_relation_brands bm.brand_model_relation) q

(** val js_ast_to_javascript : js_ast -> javascript **)

let js_ast_to_javascript =
  js_ast_to_js_top
