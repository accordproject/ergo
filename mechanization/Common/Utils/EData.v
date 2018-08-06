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

Require Import Ascii.
Require Import String.
Require Import List.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import JsAst.JsNumber.

Section EData.
  Context {m:brand_model}.

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

  Definition fmt_nl := String.String (ascii_of_N 10) EmptyString.
  Definition fmt_dq := """"%string.

  Fixpoint string_of_data (d : ergo_data) : string :=
    let jsonify := ErgoData.data_to_json_string fmt_dq in
    let string_of_rec : list (string * ergo_data) -> string :=
        fun rec =>
          ("{"%string
              ++ (String.concat
                    ", "%string
                    (map
                       (fun item =>
                          (fst item) ++ ": " ++ (string_of_data (snd item)))
                       rec))
             ++ "}"%string)%string in
    match d with
    | dunit => "nil"%string
    | dnat z => Z_to_string10 z
    | dfloat f => to_string f
    | dbool true => "true"%string
    | dbool false => "false"%string
    | dstring s => jsonify (dstring s)
    | dcoll arr =>
      "["%string
         ++ (String.concat
               ", "%string
               (map string_of_data arr))
         ++ "]"%string
    | dleft s => "some("%string ++ (string_of_data s) ++ ")"%string
    | dright _ => "none"
    | dbrand (b::nil) d' => "~"%string ++ b ++ " "%string ++ (string_of_data d')
    | dbrand _ _ => "???"%string
    | drec r => string_of_rec r 
    | dforeign _ => "???"%string
    end.

  Definition string_of_response (response : ergo_data) : string :=
    "Response. " ++ (string_of_data response) ++ fmt_nl.

  Definition string_of_emits (emits : list ergo_data) : string :=
    (fold_left
       (fun old new => ("Emit. " ++ new ++ fmt_nl ++ old)%string)
       (map (string_of_data) emits) ""%string).

  Definition string_of_state (old_state : option ergo_data) (new_state : ergo_data)
    : string :=
    let jsonify := string_of_data in
    match old_state with
    | None => "State. " ++ (jsonify new_state)
    | Some actual_old_state =>
      if Data.data_eq_dec new_state actual_old_state then
        ""%string
      else
        "State. " ++ (jsonify new_state) ++ fmt_nl
    end.

    Definition string_of_result_data (old_state : option ergo_data) (result : option ergo_data)
      : string :=
      match result with
      | None => ""
      | Some (dright msg) =>
        "Error. "%string ++ (string_of_data msg) ++ fmt_nl
      | Some out =>
        match unpack_output out with
        | Some (response, emits, state) =>
          (string_of_emits emits) ++ (string_of_response response) ++ (string_of_state old_state state)
        | None => (string_of_data out) ++ fmt_nl
        end
      end.

    Definition string_of_result_type (result : option ergoc_type)
      : string :=
      match result with
      | None => ""%string
      | Some typ => "  :  "%string ++ (ErgoCTypes.ergoc_type_to_string typ) ++ fmt_nl
      end.

    Definition string_of_result (old_state : option ergo_data) (result : (option ergoc_type * option ergo_data)) : string :=
      match result with
      | (typ, dat) => (string_of_result_data old_state dat) ++ (string_of_result_type typ)
      end.

End EData.
