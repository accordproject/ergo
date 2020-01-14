open Datatypes
open EJson
open EJsonOperators
open EJsonRuntimeOperators
open ForeignEJson
open ForeignEJsonRuntime
open ForeignToJavaScriptAst
open Imp
open ImpEJson
open JavaScriptAst
open JavaScriptAstUtil
open JsSyntax
open List0
open ListAdd

val scope : stat list -> stat

val prog_to_string : prog -> char list

val box_nat : expr -> expr

val mk_expr_error : expr

val mk_unary_expr : (expr -> expr) -> expr list -> expr

val mk_unary_op : unary_op -> expr list -> expr

val mk_binary_expr : (expr -> expr -> expr) -> expr list -> expr

val mk_binary_op : binary_op -> expr list -> expr

val mk_object : char list list -> expr list -> expr

val mk_runtime_call :
  'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> 'a2
  imp_ejson_runtime_op -> expr list -> expr

val mk_integer_plus_one :
  'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> expr -> expr

val mk_integer_le :
  'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> expr -> expr ->
  expr

val imp_ejson_op_to_js_ast : imp_ejson_op -> expr list -> expr

val cejson_to_js_ast :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> 'a1 cejson -> expr

val imp_ejson_expr_to_js_ast :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> ('a1, 'a2) imp_ejson_expr -> expr

val decl_to_js_ast :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> (var * ('a1 imp_ejson_constant, imp_ejson_op, 'a2
  imp_ejson_runtime_op) imp_expr option) -> var * expr option

val imp_ejson_stmt_to_js_ast :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> ('a1, 'a2) imp_ejson_stmt -> stat

val imp_ejson_function_to_js_ast :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
  imp_ejson_runtime_op) imp_function -> char list list * funcbody

val imp_ejson_function_to_funcelement :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
  imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> element

val imp_ejson_function_to_funcdecl :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
  imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> funcdecl

val imp_ejson_function_to_topdecl :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> char list -> ('a1 imp_ejson_constant,
  imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_function -> topdecl

val imp_ejson_to_function :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> ('a1, 'a2) imp_ejson -> topdecl list

val imp_ejson_to_method :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> ('a1, 'a2) imp_ejson -> funcdecl list

val imp_ejson_table_to_topdecls :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> char list -> ('a1, 'a2) imp_ejson list -> topdecl
  list

val imp_ejson_table_to_class :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> ('a2, 'a1)
  foreign_ejson_runtime -> char list -> ('a1, 'a2) imp_ejson -> topdecl
