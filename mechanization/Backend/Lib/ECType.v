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
Require Import List.
Require Import Qcert.Common.CommonTypes.
Require Import Qcert.Common.TypingRuntime.
Require Import ErgoSpec.Backend.Model.ErgoBackendModel.
Require Import ErgoSpec.Backend.Model.ErgoBackendRuntime.
Require Import ErgoSpec.Backend.Model.ErgoEnhancedModel.

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
  Definition ergoc_type_meet {br:brand_relation} : ectype -> ectype -> ectype := rtype_meet.
  Definition ergoc_type_join {br:brand_relation} : ectype -> ectype -> ectype := rtype_join.

  Definition ergoc_type_subtype {br:brand_relation} : ectype -> ectype -> Prop := subtype.
  Theorem ergoc_type_subtype_dec {m:brand_model}  (t1 t2:ectype) :
    {ergoc_type_subtype t1 t2} + {~ ergoc_type_subtype t1 t2}.
  Proof.
    apply subtype_dec.
  Defined.
    
  Definition untcoll {m:brand_model} : ectype -> option ectype := tuncoll.
  Definition unteither {m:brand_model} : ectype -> option (ectype * ectype) := tuneither.
  Definition untrec {m:brand_model} : ectype -> option (record_kind * (list (string * ectype))) := tunrec.

  Definition ergoc_type_infer_data {m:brand_model} : data -> Datatypes.option ectype := infer_data_type.
  Definition ergoc_type_infer_binary_op {m:brand_model} : binary_op -> ectype -> ectype -> option (ectype * ectype * ectype) := infer_binary_op_type_sub.
  Definition ergoc_type_infer_unary_op {m:brand_model} : unary_op -> ectype -> option (ectype * ectype) := infer_unary_op_type_sub.

  Definition unpack_ergoc_type {br:brand_relation} (t:ectype) : ectype_struct := proj1_sig t.
  
  Definition tbrand_relation : Set := brand_relation.
  Definition tempty_brand_relation : tbrand_relation := mkBrand_relation nil (eq_refl _) (eq_refl _).
  Definition mk_tbrand_relation : list (string * string) -> qresult tbrand_relation := Schema.mk_brand_relation.

  Definition tbrand_context_decls {br:brand_relation} : Set := brand_context_decls.
  Definition tbrand_context {br:brand_relation} : Set := brand_context.
  Definition mk_tbrand_context {br:brand_relation} : tbrand_context_decls -> tbrand_context :=
    @mk_brand_context _ br.

  Definition tbrand_model : Set := brand_model.
  Definition mk_tbrand_model {br:brand_relation} : tbrand_context_decls -> qresult tbrand_model :=
    @Schema.make_brand_model_from_decls_fails _ _ br.

  Program Definition tempty_brand_model : tbrand_model :=
    @make_brand_model _ tempty_brand_relation (mkBrand_context nil _) _.

  Definition ergoc_type_unpack {br:brand_relation} (t:ectype) : ectype_struct := proj1_sig t.

  Fixpoint rtype_to_string {br:brand_relation} (t : rtype₀) : string :=
    match t with
    | Bottom₀ => "Nothing"%string
    | Top₀ => "Any"%string
    | Unit₀ => "Unit"%string
    | Nat₀ => "Integer"%string
    | Float₀ => "Double"%string
    | Bool₀ => "Boolean"%string
    | String₀ => "String"%string
    | Coll₀ r' => (rtype_to_string r') ++ "[]"%string
    | Rec₀ k srl =>
      "{"%string ++
         (String.concat
            (", "%string)
            (map (fun sr => ((fst sr) ++ ": " ++ (rtype_to_string (snd sr)))%string)
                 srl)) ++ "}"%string
    | Either₀ tl tr => (rtype_to_string tl) ++ "?"%string
    | Arrow₀ tin tout => (rtype_to_string tin) ++ " -> "%string ++ (rtype_to_string tout)
    | Brand₀ (b::nil) => "~"%string ++ b
    | Brand₀ _ => "~"%string ++ "[multiple]"
    | Foreign₀ ft => "Foreign (probably DateTime hehe)"
    end.

  Definition ergoc_type_to_string {br:brand_relation} (t : ectype) : string :=
    rtype_to_string (ergoc_type_unpack t).

End ECType.

