open EJson
open EJsonOperators
open EJsonRuntimeOperators
open Imp

type 'foreign_ejson_model imp_ejson_constant = 'foreign_ejson_model cejson

type imp_ejson_op = ejson_op

type 'foreign_ejson_runtime_op imp_ejson_runtime_op =
  'foreign_ejson_runtime_op ejson_runtime_op

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_expr =
  ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
  'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_expr

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_stmt =
  ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
  'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_stmt

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_function =
  ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
  'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_function

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson =
  ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
  'foreign_ejson_runtime_op imp_ejson_runtime_op) imp
