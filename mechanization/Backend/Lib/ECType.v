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
  Definition tdateTime {br:brand_relation} : ectype
    := DateTime.
  Definition tduration {br:brand_relation} : ectype
    := DateTimeDuration.
  Definition tperiod {br:brand_relation} : ectype
    := DateTimePeriod.
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

  Program Definition ergoc_closed_from_open {m:brand_model} (t:ectype) : ectype :=
    match untrec t with
    | None => t
    | Some (k, fields) => Rec Closed fields _
    end.
  Next Obligation.
    assert (untrec t0 = Some (k, fields)) by auto; clear Heq_anonymous.
    generalize (tunrec_correct k t0 H); intros.
    elim H0; clear H0; intros.
    auto.
  Qed.

  (* Stricter version of brand typing -- checks that t is a subtype of the closed form for type of b *)
  Definition infer_brand_strict {m:brand_model} (b:brands) (t:ectype) : option (rtype * ectype) :=
    if (subtype_dec t (ergoc_closed_from_open (brands_type b)))
    then Some (Brand b, t)
    else None.

  Definition recminus {br:brand_relation} (rt:list (string*rtype)) (sl:list string) : list (string*rtype) :=
    fold_left rremove sl rt.

  (* Returns a pair with: fields in the expected brand not in the actual record + fields in the actual record not in the expected brand *)
  Definition diff_record_types {m:brand_model} (b:brands) (t:ectype) : option (list string * list string) :=
    match tunrec t with
    | None => None
    | Some (_, actual_rt) =>
      match tunrec (ergoc_closed_from_open (brands_type b)) with
      | None => None
      | Some (_, expected_rt) =>
        let in_expected_not_in_actual := recminus expected_rt (map fst actual_rt) in
        let in_actual_not_in_expected := recminus actual_rt (map fst expected_rt) in
        Some (map fst in_expected_not_in_actual, map fst in_actual_not_in_expected)
      end
    end.

  Fixpoint rec_fields_that_are_not_subtype {m:brand_model} (t1 t2:list (string*ectype)) : list (string * ectype * ectype) :=
    match t1, t2 with
    | nil, _ => nil
    | _, nil => nil
    | (name1,t1)::rest1, (name2,t2)::rest2 =>
      if string_dec name1 name2
      then
        if subtype_dec t2 t1
        then
          rec_fields_that_are_not_subtype rest1 rest2
        else
          (name1, t1, t2) :: rec_fields_that_are_not_subtype rest1 rest2
      else
        rec_fields_that_are_not_subtype rest1 rest2
    end.
  
  Definition fields_that_are_not_subtype {m:brand_model} (b:brands) (t:ectype) : list (string * ectype * ectype) :=
    match tunrec t with
    | None => nil
    | Some (_, actual_rt) =>
      match tunrec (ergoc_closed_from_open (brands_type b)) with
      | None => nil
      | Some (_, expected_rt) =>
        rec_fields_that_are_not_subtype expected_rt actual_rt
      end
    end.
  
End ECType.

