open ErgoWasmAst
open ErgoWasmBinary

(** val ergo_wasm_ast_to_ergo_wasm : wasm_ast -> wasm **)

let ergo_wasm_ast_to_ergo_wasm = Wasm.Encode.encode
