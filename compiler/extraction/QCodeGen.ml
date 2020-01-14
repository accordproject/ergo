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

module QCodeGen =
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 struct
  type nnrc_expr = NNRC.nnrc

  (** val nnrc_optim : nnrc_expr -> nnrc_expr **)

  let nnrc_optim x =
    x

  (** val nnrc_expr_let : var -> nnrc -> nnrc -> nnrc **)

  let nnrc_expr_let x x0 x1 =
    NNRCLet (x, x0, x1)

  (** val eindent : int -> nstring **)

  let eindent =
    indent

  (** val equotel_double : nstring **)

  let equotel_double =
    nquotel_double

  (** val eeol_newline : nstring **)

  let eeol_newline =
    neol_newline

  (** val javascript_identifier_sanitizer : char list -> char list **)

  let javascript_identifier_sanitizer =
    jsIdentifierSanitize

  type imp_ejson_function =
    (Coq_ergomodel.ergo_foreign_ejson,
    Coq_ergomodel.ergo_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function

  type imp_ejson_lib =
    (Coq_ergomodel.ergo_foreign_ejson,
    Coq_ergomodel.ergo_foreign_ejson_runtime_op) imp_ejson

  (** val nnrc_expr_to_imp_ejson_function :
      brand_model -> char list list -> CompLang.nnrc -> (enhanced_ejson,
      enhanced_foreign_ejson_runtime_op) ImpEJson.imp_ejson_function **)

  let nnrc_expr_to_imp_ejson_function bm =
    nnrc_expr_to_imp_ejson_function enhanced_foreign_type
      enhanced_foreign_runtime enhanced_foreign_ejson
      enhanced_foreign_to_ejson enhanced_foreign_to_ejson_runtime bm

  (** val imp_function_to_javascript_ast :
      brand_model -> char list -> imp_ejson_function -> CompLang.js_ast **)

  let imp_function_to_javascript_ast _ fname fbody =
    (imp_ejson_function_to_topdecl enhanced_foreign_ejson
      enhanced_foreign_ejson_to_ajavascript enhanced_foreign_ejson_runtime
      fname fbody) :: []

  (** val imp_function_table_to_javascript_ast :
      brand_model -> char list -> imp_ejson_lib -> CompLang.js_ast **)

  let imp_function_table_to_javascript_ast _ cname ftable =
    (imp_ejson_table_to_class enhanced_foreign_ejson
      enhanced_foreign_ejson_to_ajavascript enhanced_foreign_ejson_runtime
      cname ftable) :: []

  type ejavascript = javascript

  (** val nnrc_expr_to_imp_ejson :
      brand_model -> char list list -> (char list * CompLang.nnrc) ->
      (enhanced_ejson, enhanced_foreign_ejson_runtime_op) CompLang.imp_ejson **)

  let nnrc_expr_to_imp_ejson bm globals = function
  | (fname, fbody) ->
    imp_data_to_imp_ejson enhanced_foreign_type enhanced_foreign_runtime
      enhanced_foreign_ejson enhanced_foreign_to_ejson
      enhanced_foreign_to_ejson_runtime bm
      (nnrs_imp_to_imp_data enhanced_foreign_runtime fname
        (nnrs_to_nnrs_imp enhanced_foreign_runtime
          (nnrc_to_nnrs enhanced_foreign_runtime globals fbody)))

  (** val nnrc_expr_to_javascript_function :
      brand_model -> char list list -> (char list * CompLang.nnrc) ->
      CompLang.js_ast **)

  let nnrc_expr_to_javascript_function bm globals f =
    imp_ejson_to_function enhanced_foreign_ejson
      enhanced_foreign_ejson_to_ajavascript enhanced_foreign_ejson_runtime
      (nnrc_expr_to_imp_ejson bm globals f)

  (** val nnrc_expr_to_javascript_function_table :
      brand_model -> char list list -> char list -> (char list * nnrc_expr)
      list -> CompLang.js_ast **)

  let nnrc_expr_to_javascript_function_table bm globals cname ftable =
    imp_ejson_table_to_topdecls enhanced_foreign_ejson
      enhanced_foreign_ejson_to_ajavascript enhanced_foreign_ejson_runtime
      cname (map (nnrc_expr_to_imp_ejson bm globals) ftable)

  (** val js_ast_to_javascript : CompLang.js_ast -> javascript **)

  let js_ast_to_javascript =
    js_ast_to_javascript

  (** val javascript_of_inheritance :
      (char list * char list) list -> topdecl **)

  let javascript_of_inheritance h =
    Coq_constdecl
      (('i'::('n'::('h'::('e'::('r'::('i'::('t'::('a'::('n'::('c'::('e'::[]))))))))))),
      (imp_ejson_expr_to_js_ast enhanced_foreign_ejson
        enhanced_foreign_ejson_to_ajavascript enhanced_foreign_ejson_runtime
        (ImpExprOp (EJsonOpArray,
        (map (fun x -> ImpExprOp ((EJsonOpObject
          (('s'::('u'::('b'::[]))) :: (('s'::('u'::('p'::[]))) :: []))),
          ((ImpExprConst (Coq_cejstring (fst x))) :: ((ImpExprConst
          (Coq_cejstring (snd x))) :: [])))) h)))))

  type java = CompLang.java

  (** val java_identifier_sanitizer : char list -> char list **)

  let java_identifier_sanitizer =
    javaIdentifierSanitize

  (** val nnrc_expr_to_java :
      NNRC.nnrc -> int -> int -> nstring -> nstring -> (char list * nstring)
      list -> (nstring * java_json) * int **)

  let nnrc_expr_to_java =
    nnrcToJava enhanced_foreign_runtime enhanced_foreign_to_java

  (** val nnrc_expr_java_unshadow :
      NNRC.nnrc -> int -> int -> nstring -> nstring -> var list ->
      (char list * nstring) list -> (nstring * java_json) * int **)

  let nnrc_expr_java_unshadow =
    nnrcToJavaunshadow enhanced_foreign_runtime enhanced_foreign_to_java

  (** val nnrc_expr_to_java_method :
      char list -> nnrc_expr -> int -> nstring -> nstring ->
      (char list * nstring) list -> nstring -> nstring **)

  let nnrc_expr_to_java_method input_v e i eol quotel ivs =
    let e0 =
      closeFreeVars enhanced_foreign_runtime ('_'::[])
        java_identifier_sanitizer (NNRCVar input_v) e (map fst ivs)
    in
    nnrcToJavaFun enhanced_foreign_runtime enhanced_foreign_to_java i input_v
      e0 eol quotel ivs

  type java_data = java_json

  (** val mk_java_data : nstring -> java_json **)

  let mk_java_data x =
    x

  (** val from_java_data : java_data -> nstring **)

  let from_java_data =
    from_java_json
 end
