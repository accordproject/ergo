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
Require Import Qcert.Data.DataRuntime.
Require Import Qcert.JSON.JSONSystem.
Require Import Qcert.Translation.Model.DataToEJson.
Require Import Qcert.Translation.Model.EJsonToJSON.

Require Import ErgoSpec.Backend.Lib.QBackendModel.
Require Import ErgoSpec.Backend.Lib.QBackendRuntime.

Module QData(ergomodel:QBackendModel).
  
  Definition json : Set 
    := JSON.json.
  Definition data : Set 
    := Data.data.
  Definition t : Set 
    := data.
  
  Definition jnull : json
    := JSON.jnull.
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

  Definition dsome : data -> data
    := Data.dsome.
  Definition dnone : data
    := Data.dnone.
  
  Definition dsuccess : data -> data
    := Data.dleft.
  Definition derror : data -> data
    := Data.dright.
  
  (** data -> JSON *string* conversion *)
  (* XXX TO DO ?
  Definition data_to_json_string s : Data.data -> String.string 
    := ergomodel.ergo_data_to_json_string s.

  Definition json_to_json_string s : json -> String.string 
    := JSON.jsonToJS s.
*)

End QData.

