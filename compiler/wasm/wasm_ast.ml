(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

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

let ergo_imp_ejson_to_wasm_ast hierarchy (m : ErgoImp.ergo_imp_module) =
  match m.modulei_declarations with
  | [ DIFuncTable (_ , lib)] -> imp_ejson_to_wasm_ast hierarchy lib
  | _ -> failwith "unsupported ergo imp module"
