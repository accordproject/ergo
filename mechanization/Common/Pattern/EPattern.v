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

Require Import String.

Require Import ErgoSpec.Backend.ErgoBackend.

Section EPattern.
  Local Open Scope string.

  Definition type_annotation : Set := option string.
  
  Inductive ergo_pattern :=
  | CaseData : ErgoData.data -> ergo_pattern            (**r match against value *)
  | CaseWildcard : type_annotation -> ergo_pattern      (**r match anything *)
  | CaseLet : string -> type_annotation -> ergo_pattern (**r match against type *)
  | CaseLetOption : string -> type_annotation -> ergo_pattern (**r match against type *)
  .

End EPattern.
