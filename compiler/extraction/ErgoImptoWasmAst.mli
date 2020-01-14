open BrandRelation
open ErgoImp
open ErgoWasmAst
open TBrandModel

val ergo_imp_ejson_to_wasm_ast :
  brand_relation_t -> ergo_imp_module -> wasm_ast

val ergo_imp_ejson_to_wasm_ast_typed :
  brand_model -> ergo_imp_module -> wasm_ast

val ergo_imp_module_to_wasm_ast :
  brand_model -> char list -> ergo_imp_module -> wasm_ast
