type t = Wasm.Ast.module_

module ImpEJson = struct
  include EJson
  include EJsonOperators
  include EJsonRuntimeOperators
  include Imp

  (* TODO: why is this in QCert ImpEJson but not in Ergo ImpEJson? *)
  type 'foreign_ejson_model imp_ejson_model = 'foreign_ejson_model ejson
  include ImpEJson
end

include Qcert_lib.Wasm_backend.Make(ImpEJson)

let ergo_imp_ejson_to_wasm_ast (m : ErgoImp.ergo_imp_module) =
  match m.modulei_declarations with
  | [ DIFuncTable (_ , lib)] -> imp_ejson_to_wasm_ast lib
  | _ -> failwith "unsupported ergo imp module"
