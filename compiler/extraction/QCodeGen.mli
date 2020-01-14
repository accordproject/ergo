open CompCorrectness
open CompDriver
open CompLang
open Datatypes
open EJson
open EJsonOperators
open EmitUtil
open Imp
open ImpEJson
open ImpEJsontoJavaScriptAst
open Java
open JavaScriptAst
open List0
open NNRC
open NNRCtoJava
open NativeString
open QcertData
open QcertDataToEJson
open QcertEJson
open QcertToJava
open QcertToJavascriptAst
open QcertType
open TBrandModel
open Var
open CNNRC
open CNNRCShadow

module QCodeGen :
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 sig
  type nnrc_expr = NNRC.nnrc

  val nnrc_optim : nnrc_expr -> nnrc_expr

  val nnrc_expr_let : var -> nnrc -> nnrc -> nnrc

  val eindent : int -> nstring

  val equotel_double : nstring

  val eeol_newline : nstring

  val javascript_identifier_sanitizer : char list -> char list

  type imp_ejson_function =
    (Coq_ergomodel.ergo_foreign_ejson,
    Coq_ergomodel.ergo_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function

  type imp_ejson_lib =
    (Coq_ergomodel.ergo_foreign_ejson,
    Coq_ergomodel.ergo_foreign_ejson_runtime_op) imp_ejson

  val nnrc_expr_to_imp_ejson_function :
    brand_model -> char list list -> CompLang.nnrc -> (enhanced_ejson,
    enhanced_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function

  val imp_function_to_javascript_ast :
    brand_model -> char list -> imp_ejson_function -> CompLang.js_ast

  val imp_function_table_to_javascript_ast :
    brand_model -> char list -> imp_ejson_lib -> CompLang.js_ast

  type ejavascript = javascript

  val nnrc_expr_to_imp_ejson :
    brand_model -> char list list -> (char list * CompLang.nnrc) ->
    (enhanced_ejson, enhanced_foreign_ejson_runtime_op) CompLang.imp_ejson

  val nnrc_expr_to_javascript_function :
    brand_model -> char list list -> (char list * CompLang.nnrc) ->
    CompLang.js_ast

  val nnrc_expr_to_javascript_function_table :
    brand_model -> char list list -> char list -> (char list * nnrc_expr)
    list -> CompLang.js_ast

  val js_ast_to_javascript : CompLang.js_ast -> javascript

  val javascript_of_inheritance : (char list * char list) list -> topdecl

  type java = CompLang.java

  val java_identifier_sanitizer : char list -> char list

  val nnrc_expr_to_java :
    NNRC.nnrc -> int -> int -> nstring -> nstring -> (char list * nstring)
    list -> (nstring * java_json) * int

  val nnrc_expr_java_unshadow :
    NNRC.nnrc -> int -> int -> nstring -> nstring -> var list ->
    (char list * nstring) list -> (nstring * java_json) * int

  val nnrc_expr_to_java_method :
    char list -> nnrc_expr -> int -> nstring -> nstring ->
    (char list * nstring) list -> nstring -> nstring

  type java_data = java_json

  val mk_java_data : nstring -> java_json

  val from_java_data : java_data -> nstring
 end
