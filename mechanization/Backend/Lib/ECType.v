(*
 * Copyright 2015-2016 IBM Corporation
 *
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
Require Import Qcert.Common.CommonTypes.
Require Import Qcert.Common.TypingRuntime.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.

Module ECType(ergomodel:ErgoBackendModel).

  Definition empty_brand_model (x:unit) := TBrandModel.empty_brand_model.

  Definition record_kind : Set
    := RType.record_kind.

  Definition open_kind : record_kind
    := RType.Open.

  Definition closed_kind : record_kind
    := RType.Closed.

  Definition ectype_struct {m:brand_relation} : Set
    := RType.rtype₀.
  Definition ectype {m:brand_relation} : Set
    := RType.rtype.
  Definition t {m:brand_relation} : Set
    := ectype.

  Definition sorted_pf_type {m:brand_relation} srl
      := SortingAdd.is_list_sorted Bindings.ODT_lt_dec (@Assoc.domain String.string ectype srl) = true.

  Definition Bottom {m:brand_relation} : ectype
    := RType.Bottom.  
  Definition Top {m:brand_relation} : ectype
    := RType.Top.
  Definition Unit {m:brand_relation} : ectype
    := RType.Unit.
  Definition Float {m:brand_relation} : ectype
    := RType.Float.
  Definition Integer {m:brand_relation} : ectype
    := RType.Nat.
  Definition Bool {m:brand_relation} : ectype
    := RType.Bool.
  Definition String {m:brand_relation} : ectype
    := RType.String.
  Definition Coll {m:brand_relation} : ectype -> ectype
    := RType.Coll.
  Definition Rec {m:brand_relation} : record_kind -> forall (r:list (String.string*ectype)), sorted_pf_type r -> ectype
    := RType.Rec.
  Definition Either {m:brand_relation} : ectype -> ectype -> ectype
    := RType.Either.
  Definition Arrow {m:brand_relation} : ectype -> ectype -> ectype
    := RType.Arrow.
  Definition Brand {m:brand_relation} : list String.string -> ectype 
    := RType.Brand.

  Definition Option {m:brand_relation} : ectype -> ectype
    := RType.Option.
  
  (* Additional support for brand models extraction -- will have to be tested/consolidated *)

  Definition brand_context_type {m:brand_relation} : Set := (String.string*ectype).
  
  Definition brand_relation : Set := brand_relation.
  Definition make_brand_relation := Schema.mk_brand_relation.
  Definition brand_model : Set := brand_model.
  Definition make_brand_model := Schema.make_brand_model_from_decls_fails.
  Definition typing_runtime : Set := typing_runtime.

End ECType.

