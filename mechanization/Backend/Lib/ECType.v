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

  Definition ectype_struct {br:brand_relation} : Set
    := RType.rtype₀.
  Definition ectype {br:brand_relation} : Set
    := RType.rtype.
  Definition t {br:brand_relation} : Set
    := ectype.

  Definition sorted_pf_type {br:brand_relation} srl
      := SortingAdd.is_list_sorted Bindings.ODT_lt_dec (@Assoc.domain String.string ectype srl) = true.

  Definition tbottom {br:brand_relation} : ectype
    := RType.Bottom.  
  Definition ttop {br:brand_relation} : ectype
    := RType.Top.
  Definition tunit {br:brand_relation} : ectype
    := RType.Unit.
  Definition tfloat {br:brand_relation} : ectype
    := RType.Float.
  Definition tnat {br:brand_relation} : ectype
    := RType.Nat.
  Definition tbool {br:brand_relation} : ectype
    := RType.Bool.
  Definition tstring {br:brand_relation} : ectype
    := RType.String.
  Definition tcoll {br:brand_relation} : ectype -> ectype
    := RType.Coll.
  Definition trec {br:brand_relation} : record_kind -> forall (r:list (String.string*ectype)), sorted_pf_type r -> ectype
    := RType.Rec.
  Definition teither {br:brand_relation} : ectype -> ectype -> ectype
    := RType.Either.
  Definition tarrow {br:brand_relation} : ectype -> ectype -> ectype
    := RType.Arrow.
  Definition tbrand {br:brand_relation} : list String.string -> ectype 
    := RType.Brand.

  Definition toption {br:brand_relation} : ectype -> ectype
    := RType.Option.

  (* Support for type checking *)
  Definition tmeet {br:brand_relation} : ectype -> ectype -> ectype := rtype_meet.
  Definition tjoin {br:brand_relation} : ectype -> ectype -> ectype := rtype_meet.

  Definition tsubtype {br:brand_relation} : ectype -> ectype -> Prop := subtype.
  Theorem tsubtype_dec {m:brand_model}  (t1 t2:ectype) :
    {tsubtype t1 t2} + {~ tsubtype t1 t2}.
  Proof.
    apply subtype_dec.
  Defined.
    
  Definition untcoll {m:brand_model} : ectype -> option ectype := tuncoll.
  Definition unteither {m:brand_model} : ectype -> option (ectype * ectype) := tuneither.
  Definition untrec {m:brand_model} : ectype -> option (record_kind * (list (string * ectype))) := tunrec.

  Definition tinfer_data {m:brand_model} : data -> Datatypes.option ectype := infer_data_type.
  Definition tinfer_binary_op {m:brand_model} : binary_op -> ectype -> ectype -> option (ectype * ectype * ectype) := infer_binary_op_type_sub.
  Definition tinfer_unary_op {m:brand_model} : unary_op -> ectype -> option (ectype * ectype) := infer_unary_op_type_sub.

End ECType.

