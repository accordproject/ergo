open BinaryOperators
open BrandRelation
open DataNorm
open DataToEJson
open Datatypes
open EJson
open EJsonOperators
open EJsonRuntimeOperators
open Encode
open ForeignDataToEJson
open ForeignEJson
open ForeignEJsonRuntime
open ForeignRuntime
open ForeignToEJsonRuntime
open Imp
open ImpData
open ImpEJson
open Lift
open List0
open SortingDesc
open UnaryOperators

val mk_imp_ejson_expr_error : char list -> ('a1, 'a2) imp_ejson_expr

val mk_imp_ejson_op :
  imp_ejson_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
  imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr

val mk_imp_ejson_runtime_call :
  'a2 imp_ejson_runtime_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
  imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr

val mk_string : char list -> ('a1, 'a2) imp_ejson_expr

val mk_left :
  ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
  -> ('a1, 'a2) imp_ejson_expr

val mk_right :
  ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
  -> ('a1, 'a2) imp_ejson_expr

val mk_array :
  ('a1 imp_ejson_constant, imp_ejson_op, 'a2 imp_ejson_runtime_op) imp_expr
  list -> ('a1, 'a2) imp_ejson_expr

val mk_object :
  (char list * ('a1, 'a2) imp_ejson_expr) list -> ('a1, 'a2) imp_ejson_expr

val mk_string_array : char list list -> ('a1, 'a2) imp_ejson_expr

val ejson_to_expr : 'a1 ejson -> ('a1, 'a2) imp_ejson_expr

val sortCriterias_to_ejson_expr :
  (char list * coq_SortDesc) list -> ('a1, 'a2) imp_ejson_expr

val brands_to_ejson_expr : char list list -> ('a1, 'a2) imp_ejson_expr

val mk_either_expr :
  ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr

val mk_to_left_expr :
  ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr

val mk_to_right_expr :
  ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2) imp_ejson_expr

val imp_data_unary_op_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> unary_op -> ('a1, 'a2) imp_ejson_expr list -> ('a1,
  'a2) imp_ejson_expr

val imp_data_binary_op_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  binary_op -> ('a1 imp_ejson_constant, imp_ejson_op, 'a2
  imp_ejson_runtime_op) imp_expr list -> ('a1, 'a2) imp_ejson_expr

val imp_data_op_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> imp_data_op -> ('a1, 'a2) imp_ejson_expr list -> ('a1,
  'a2) imp_ejson_expr

val imp_data_runtime_call_to_imp_ejson :
  imp_data_runtime_op -> ('a1, 'a2) imp_ejson_expr list -> ('a1, 'a2)
  imp_ejson_expr

val imp_data_expr_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> imp_data_expr -> ('a1, 'a2) imp_ejson_expr

val imp_data_stmt_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> imp_data_stmt -> ('a1, 'a2) imp_ejson_stmt

val imp_data_function_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> imp_data_function -> ('a1, 'a2) imp_ejson_function

val imp_data_to_imp_ejson :
  foreign_runtime -> 'a1 foreign_ejson -> ('a1, 'a2) foreign_to_ejson ->
  ('a2, 'a1) foreign_ejson_runtime -> ('a1, 'a2) foreign_to_ejson_runtime ->
  brand_relation_t -> imp_data -> ('a1, 'a2) imp_ejson
