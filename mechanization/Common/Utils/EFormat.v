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
Require Import List.
Require Import Basics.

Require Import Coq.Strings.Ascii.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Translation.ErgoNameResolve.

Require Import Common.Utils.EResult.
Require Import Common.Utils.EUtil.
Require Import Common.Utils.EProvenance.

Require Import Ergo.

Section EFormat.


Definition ergo_string_of_location_point (lp : location_point) : string :=
  (toString lp.(line)) ++ ":" ++ (toString lp.(column)).

Definition ergo_string_of_location (loc : location) : string :=
  let file :=
      match loc.(loc_file) with
      | Some f => (f ++ " ")%string
      | None => ""%string
      end
  in
  file ++
  (ergo_string_of_location_point loc.(loc_start)) ++ "-" ++
  (ergo_string_of_location_point loc.(loc_end)).

Definition ergo_format_error (name : string) (prov : provenance) (msg : string) :=
  let loc := loc_of_provenance prov in
  (name ++ " at " ++ (ergo_string_of_location loc) ++ " '" ++ msg ++ "'")%string.

Definition ergo_string_of_error (err : eerror) : string :=
  match err with
  | SystemError loc s => "System error: " ++ s
  | ParseError loc msg => ergo_format_error "Parse error" loc msg
  | CompilationError loc msg => ergo_format_error "Compilation error" loc msg
  | TypeError loc msg => ergo_format_error "Type error" loc msg
  | RuntimeError loc msg => ergo_format_error "Runtime error" loc msg
  end.

Definition fmt_nl := "
"%string.

Definition fmt_esc := String.String (ascii_of_N 27) EmptyString.

Definition fmt_csi : string := fmt_esc ++ ("["%string).

Definition fmt_red (msg : string) : string :=
  (fmt_csi ++ "31m" ++ msg ++ fmt_esc ++ fmt_csi ++ "0m")%string.

Definition fmt_grn (msg : string) : string :=
  (fmt_csi ++ "32m" ++ msg ++ fmt_esc ++ fmt_csi ++ "0m")%string.

Definition fmt_mag (msg : string) : string :=
  (fmt_csi ++ "35m" ++ msg ++ fmt_esc ++ fmt_csi ++ "0m")%string.

Definition ergo_string_of_result {A : Set} (result : eresult (A * ergo_context * option ergo_data)) : string :=
  match result with
  | Success _ _ (_, _, None) => ""
  | Success _ _ (_, _, Some
                         (dleft
                            (drec (("response"%string, response)
                                     ::("state"%string, state)
                                     ::("emit"%string, dcoll emits)
                                     ::nil))
                            )
                ) =>
    (fold_left
       (fun old new => ((fmt_mag "Emit. ") ++ new ++ fmt_nl ++ old)%string)
       (map (ErgoData.data_to_json_string """"%string) emits) ""%string)
      ++ (fmt_grn "Response. ") ++ (ErgoData.data_to_json_string """"%string response)
    (*dataToString d*) 
  | Success _ _ (_, _, Some
                         (dright msg)
                ) =>
    fmt_red ("Error. "%string) ++ (ErgoData.data_to_json_string """"%string msg)
  | Success _ _ (_, _, Some d) =>
    ErgoData.data_to_json_string """"%string d
  | Failure _ _ f => ergo_string_of_error f
  end.

End EFormat.
