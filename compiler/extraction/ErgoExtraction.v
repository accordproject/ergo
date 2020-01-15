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

(* Ergo Compiler Extraction *)

(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import Qcert.Extraction.ExtrOcamlFloatNatIntZInt.

Extraction Blacklist String List.

Require Import Qcert.Utils.Digits.
Extract Constant Digits.nat_to_string10 => "(fun x -> Util.char_list_of_string (string_of_int x))".
Extract Constant Digits.Z_to_string10 => "(fun x -> Util.char_list_of_string (string_of_int x))".

Extract Constant String.append => "(fun s1 s2 -> Util.char_list_append s1 s2)".

Require Import ErgoSpec.Utils.Misc.
Extract Constant Misc.coq_distinct => "(fun name l -> Util.coq_distinct name l)".
Extract Constant Misc.coq_toposort => "(fun label file g -> Util.coq_toposort label file g)".
Extract Constant Misc.coq_sort_given_topo_order => "(fun labely labelx file order l -> Util.coq_sort_given_topo_order labely labelx file order l)".
Extract Constant Misc.coq_time => "(fun msg f x -> Util.coq_time msg f x)".
Extract Constant Misc.get_local_part => "(fun name -> Util.get_local_part name)".
Extract Constant Misc.find_duplicate => "(fun l -> Util.find_duplicate l)".
Extract Constant Misc.coq_print_warnings => "(fun prefix warnings x -> Util.coq_print_warnings prefix warnings x)".

(* Ergo modules *)
Require ErgoCompiler.
Extraction "core" ErgoCompiler.ErgoCompiler.
