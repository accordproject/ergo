open ErgoImp
open Qcert_lib.Wasm_translate

let ergo_imp emodule =
  match emodule.modulei_declarations with
  | [DIFuncTable (name,functions)] ->
(*      imp functions *)
      failwith ("ErgoImp -> Wasm TBD")
  | _ ->
      failwith ("ErgoImp -> Wasm TBD")

