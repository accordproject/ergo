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

open ErgoComp.ErgoCompiler

let my_init_repl_context input =
  begin match brand_model_from_inputs input with
  | Success bm -> init_repl_context bm input
  | Failure e -> ErgoUtil.ergo_raise e
  end
let my_ergo_repl_eval_decl rctxt decl =
  ergo_repl_eval_decl rctxt.ErgoComp.repl_context_comp_ctxt.ErgoComp.compilation_context_brand_model rctxt decl

