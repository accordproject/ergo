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

Require String.
Require Qcert.Common.CommonRuntime.
Require Qcert.Utils.JSON.
Require Qcert.Common.Data.DatatoJSON.
Require Qcert.Translation.NNRCtoJavaScript.

Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.

Module EData(ergomodel:ErgoBackendModel).
  
  Definition json : Set 
    := JSON.json.
  Definition data : Set 
    := Data.data.
  Definition t : Set 
    := data.
  
  Definition jnil : json
    := JSON.jnil.
  Definition jnumber z : json 
    := JSON.jnumber z.
  Definition jbool b : json 
    := JSON.jbool b.
  Definition jstring s : json
    := JSON.jstring s.
  Definition jarray jl : json
    := JSON.jarray jl.
  Definition jobject jl : json
    := JSON.jobject jl.

  Definition dunit : data 
    := Data.dunit.
  Definition dnat z : data 
    := Data.dnat z.
  Definition dfloat f : data 
    := Data.dfloat f.
  Definition dbool b : data 
    := Data.dbool b.
  Definition dstring s : data 
    := Data.dstring s.
  Definition dcoll dl : data 
    := Data.dcoll dl.
  Definition drec dl : data 
    := Data.drec dl.
  Definition dleft : data -> data 
    := Data.dleft.
  Definition dright : data -> data 
    := Data.dright.
  Definition dbrand b : data -> data 
    := Data.dbrand b.
  (* foreign data is supported via the model *)

  (** data -> JSON *string* conversion *)
  Definition data_to_json_string s : data -> String.string 
    := ergomodel.ergo_data_to_json_string s.
  Definition json_to_json_string s : json -> String.string 
    := JSON.jsonToJS s.

End EData.

