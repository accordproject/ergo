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

open Core.ErgoCompiler

let repl_bm = ref ergo_empty_brand_model
let my_init_repl_context input =
  begin match ergo_brand_model_from_inputs input with
  | Success ((bm,_),warnings) -> repl_bm := bm; init_repl_context !repl_bm input
  | Failure e -> Ergo_util.ergo_raise e
  end
let my_ergo_repl_eval_decl rctxt decl =
  begin match ergo_refresh_brand_model !repl_bm rctxt with
  | Success ((bm, rctxt'),warnings) ->
      repl_bm := bm;
      ergo_repl_eval_decl
        !repl_bm
        rctxt'
        decl
  | Failure e -> Ergo_util.ergo_raise e
  end

