open BrandRelation
open ErgoImp
open ErgoWasmAst
open TBrandModel

(** val ergo_imp_ejson_to_wasm_ast :
    brand_relation_t -> ergo_imp_module -> wasm_ast **)

let ergo_imp_ejson_to_wasm_ast = Wasm_ast.ergo_imp_ejson_to_wasm_ast

(** val ergo_imp_ejson_to_wasm_ast_typed :
    brand_model -> ergo_imp_module -> wasm_ast **)

let ergo_imp_ejson_to_wasm_ast_typed bm =
  ergo_imp_ejson_to_wasm_ast (brand_relation_brands bm.brand_model_relation)

(** val ergo_imp_module_to_wasm_ast :
    brand_model -> char list -> ergo_imp_module -> wasm_ast **)

let ergo_imp_module_to_wasm_ast bm _ p =
  ergo_imp_ejson_to_wasm_ast_typed bm p
