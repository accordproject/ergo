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
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EResult.

Section EData.

  Definition unpack_output
             (out : ergo_data)
  : option (ergo_data * list ergo_data * ergo_data) :=
    match out with
    | (dleft (drec (("response"%string, response)
                      ::("state"%string, state)
                      ::("emit"%string, dcoll emits)
                      ::nil))) =>
      Some (response, emits, state)
    | _ => None
    end.

  Definition string_of_response (response : ergo_data) : string :=
    (fmt_grn "Response. ") ++ (ErgoData.data_to_json_string fmt_dq response) ++ fmt_nl.

  Definition string_of_emits (emits : list ergo_data) : string :=
    (fold_left
       (fun old new => ((fmt_mag "Emit. ") ++ new ++ fmt_nl ++ old)%string)
       (map (ErgoData.data_to_json_string fmt_dq) emits) ""%string).

  Definition string_of_state (old_state : option ergo_data) (new_state : ergo_data)
    : string :=
    let jsonify := ErgoData.data_to_json_string fmt_dq in
    match old_state with
    | None => (fmt_blu "State. ") ++ (jsonify new_state)
    | Some actual_old_state =>
      if Data.data_eq_dec new_state actual_old_state then
        ""%string
      else
        (fmt_blu "State. ") ++ (jsonify new_state) ++ fmt_nl
    end.

    (* XXX May be nice to replace by a format that aligns with Ergo notations instead of JSON and move to an earlier module e.g., Common/Utils/EData *)
    Definition string_of_result (old_state : option ergo_data) (result : option ergo_data)
      : string :=
      match result with
      | None => ""
      | Some (dright msg) =>
        fmt_red ("Error. "%string) ++ (ErgoData.data_to_json_string fmt_dq msg) ++ fmt_nl
      | Some out =>
        match unpack_output out with
        | Some (response, emits, state) =>
          
          (string_of_emits emits) ++ (string_of_response response) ++ (string_of_state old_state state)
        | None => (ErgoData.data_to_json_string fmt_dq out) ++ fmt_nl
        end
(* Note: this was previously powered by QCert's dataToString d, and I kind of
   liked that better anyway, so we might transition back at some point. The
   problem was that QCert treated arrays as bags and sorted them before
   printing (!!!). *)
      end.

End EData.
