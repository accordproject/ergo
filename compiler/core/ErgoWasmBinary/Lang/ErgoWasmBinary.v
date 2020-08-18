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

(** ErgoWasm is an IL for Wasm *)

(** * Abstract Syntax *)

Require Import Qcert.WasmBinary.Lang.WasmBinary.

Section ErgoWasmBinary.
  (** WASM programs are in AST form *)
  (** Same type as in Q*cert *)
  Definition wasm : Set := wasm.
  Axiom wasm_to_string : wasm -> Qcert.Utils.NativeString.nstring.

End ErgoWasmBinary.

Extract Constant wasm => "string".
Extract Constant wasm_to_string => "(fun x -> Base64.encode_string x)".
