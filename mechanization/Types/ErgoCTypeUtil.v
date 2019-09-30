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

(* Support for ErgoType models *)

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.

Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Common.PrintTypedData.

Section ErgoCTypeUtil.
  Context {m : brand_model}.

  Import ErgoCType.

  Definition ergoc_type_join_safe prov (t1 t2:ergoc_type) : eresult ergoc_type :=
    let jt := ergoc_type_join t1 t2 in
    if ergoc_type_subtype_dec ttop jt
    then efailure (ETypeError prov ("Join between types is TOP.")%string)
    else esuccess jt nil.

  Definition ergoc_type_meet_safe prov (t1 t2:ergoc_type) : eresult ergoc_type :=
    let jt := ergoc_type_meet t1 t2 in
    if ergoc_type_subtype_dec jt tbottom
    then efailure (ETypeError prov ("Meet between types is BOTTOM.")%string)
    else esuccess jt nil.

  Program Definition empty_rec_type : ergoc_type := Rec Closed nil _.

  Definition ergo_format_unop_error nsctxt (op : unary_op) (arg : ergoc_type) : string :=
    let fmt_easy :=
        fun name expected actual =>
          ("Operator `" ++ name ++ "' expected an operand of type `" ++
                        (ergoc_type_to_string nsctxt expected) ++
                        "' but received an operand of type `" ++
                        (ergoc_type_to_string nsctxt actual) ++ "'.")%string
    in
    match op with
    | OpNeg => fmt_easy "!"%string tbool arg
    | OpFloatUnary FloatNeg => fmt_easy "-"%string tfloat arg
    | OpDot name => "The field `" ++ name ++ "' does not exist in type `" ++ (ergoc_type_to_string nsctxt arg) ++ "'"
    | OpIdentity | OpRec _ | OpBag
    | OpLeft | OpRight | OpBrand _ | OpUnbrand | OpCast _ =>
      "This operator received an unexpected argument of type `" ++ (ergoc_type_to_string nsctxt arg) ++ "'"
    | OpRecRemove _ | OpRecProject _
    | OpSingleton | OpFlatten | OpDistinct | OpOrderBy _
    | OpCount | OpToString | OpToText | OpLength | OpSubstring _ _ | OpLike _ _
    | OpNatUnary _ | OpNatSum | OpNatMin | OpNatMax | OpNatMean | OpFloatOfNat
    | OpFloatUnary _ | OpFloatTruncate | OpFloatSum | OpFloatMean | OpFloatBagMin | OpFloatBagMax
    | OpForeignUnary _ =>
      "This function received an unexpected argument of type `" ++ (ergoc_type_to_string nsctxt arg) ++ "'"
    end.

  Definition ergo_format_binop_error nsctxt (op : binary_op) (arg1 : ergoc_type) (arg2 : ergoc_type) : string :=
    let fmt_easy :=
        fun name e1 e2 =>
          ("Operator `" ++ name ++ "' expected operands of type `" ++
                        (ergoc_type_to_string nsctxt e1) ++ "' and `" ++
                        (ergoc_type_to_string nsctxt e2) ++
                        "' but received operands of type `" ++
                        (ergoc_type_to_string nsctxt arg1) ++ "' and `" ++
                        (ergoc_type_to_string nsctxt arg2) ++ "'.")%string
    in
    match op with
    | OpAnd => fmt_easy "and"%string tbool tbool
    | OpOr => fmt_easy "or"%string tbool tbool
    | OpLt => fmt_easy "<"%string tnat tnat
    | OpLe => fmt_easy "<="%string tnat tnat
    | OpFloatBinary FloatPlus => fmt_easy "+"%string tfloat tfloat
    | OpFloatBinary FloatMinus => fmt_easy "-"%string tfloat tfloat
    | OpFloatBinary FloatMult => fmt_easy "*"%string tfloat tfloat
    | OpFloatBinary FloatDiv => fmt_easy "/"%string tfloat tfloat
    | OpFloatBinary FloatPow => fmt_easy "^"%string tfloat tfloat
    | OpNatBinary NatPlus => fmt_easy "+"%string tnat tnat
    | OpNatBinary NatMinus => fmt_easy "-"%string tnat tnat
    | OpNatBinary NatMult => fmt_easy "*"%string tnat tnat
    | OpNatBinary NatDiv => fmt_easy "/"%string tnat tnat
    | OpNatBinary NatPow => fmt_easy "^"%string tnat tnat
    | OpFloatCompare FloatLt => fmt_easy "<"%string tfloat tfloat
    | OpFloatCompare FloatLe => fmt_easy "<="%string tfloat tfloat
    | OpFloatCompare FloatGt => fmt_easy ">"%string tfloat tfloat
    | OpFloatCompare FloatGe => fmt_easy ">="%string tfloat tfloat
    | OpRecConcat | OpRecMerge
    | OpEqual | OpStringConcat | OpStringJoin
      => "This operator received unexpected arguments of type `" ++ (ergoc_type_to_string nsctxt arg1) ++ "' " ++ " and `" ++ (ergoc_type_to_string nsctxt arg2) ++ "'."
    | OpBagUnion | OpBagDiff | OpBagMin | OpBagMax | OpBagNth | OpContains
    | OpFloatBinary FloatMin | OpFloatBinary FloatMax
    | OpForeignBinary _
      => "This function received unexpected arguments of type `" ++ (ergoc_type_to_string nsctxt arg1) ++ "' " ++ " and `" ++ (ergoc_type_to_string nsctxt arg2) ++ "'."
    end.

  Definition ergo_format_unary_operator_dispatch_error nsctxt (op : ergo_unary_operator)
     (arg : ergoc_type) : string :=
    "This operator received an unexpected argument of type `" ++ (ergoc_type_to_string nsctxt arg) ++ "'.".

  Definition ergo_format_binary_operator_dispatch_error nsctxt (op : ergo_binary_operator)
     (arg1 : ergoc_type) (arg2 : ergoc_type) : string :=
    "This operator received unexpected arguments of type `" ++ (ergoc_type_to_string nsctxt arg1) ++ "' " ++ " and `" ++ (ergoc_type_to_string nsctxt arg2) ++ "'.".

  Definition ergo_format_new_error nsctxt (name:string) (actual:ergoc_type) : string :=
    let concept_name := ergoc_type_to_string nsctxt (Brand (name::nil)) in
    (* First check if all the fields are present and no extra field is present *)
    match diff_record_types (name::nil) actual with
    | None => "Concept name " ++ name ++ " does not match data"
    | Some (nil, nil) =>
      (* If all the fields are right, check if any of them is not a subtype *)
      match fields_that_are_not_subtype (name::nil) actual with
      | nil => "Concept " ++ name ++ " doesn't match data (one field is not a subtype)"
      | (expected_name, expected_type, actual_type) :: _ =>
        "Field `" ++ expected_name
                  ++ "' has type `" ++ (ergoc_type_to_string nsctxt actual_type)
                  ++ "' but should have type `" ++ (ergoc_type_to_string nsctxt expected_type) ++ "'"
      end
    | Some (nil, actual_name::nil) =>
      "Unknown field `" ++ actual_name ++ "' in type `" ++ concept_name ++ "'"
    | Some (nil, actual_names) =>
      "Unknown fields `" ++ String.concat "', `" actual_names ++ "' in type `" ++ concept_name ++ "'"
    | Some (expected_name::nil, _) =>
      "Missing field `" ++ expected_name ++ "' in type `" ++ concept_name ++ "'"
    | Some (expected_names, _) =>
      "Missing fields `" ++ String.concat "', `" expected_names ++ "' in type `" ++ concept_name ++ "'"
    end.

  Definition ergo_format_clause_return_fallback_error
             nsctxt
             (name:string)
             (actual expected:ergoc_type) : string :=
    let actual_s := ergoc_type_to_string nsctxt actual in
    let expected_s := ergoc_type_to_string nsctxt expected in
    "Clause " ++ name ++ " should return `" ++ expected_s
              ++ "' but actually returns `" ++ actual_s ++ "'".

  Definition ergo_format_clause_return_component_error
             nsctxt
             (name:string)
             (component1 component2:string)
             (actual expected:ergoc_type) : string :=
    let actual_s := ergoc_type_to_string nsctxt actual in
    let expected_s := ergoc_type_to_string nsctxt expected in
    "Clause " ++ name ++ " should " ++ component1 ++ " `" ++ expected_s
              ++ "' but actually " ++ component2 ++ " `" ++ actual_s ++ "'".

  Definition ergo_format_clause_return_normal_error
             nsctxt
             (name:string)
             (actual expected:ergoc_type)
             (actual_quad expected_quad:ergoc_type * ergoc_type * ergoc_type * ergoc_type)
    : string :=
    let '(actual_resp, actual_emit, actual_state, actual_error) := actual_quad in
    let '(expected_resp, expected_emit, expected_state, expected_error) := expected_quad in
    if ergoc_type_subtype_dec actual_resp expected_resp
    then
      if ergoc_type_subtype_dec actual_emit expected_emit
      then
        if ergoc_type_subtype_dec actual_state expected_state
        then
          if ergoc_type_subtype_dec actual_error expected_error
          then
            ergo_format_clause_return_fallback_error nsctxt name actual expected
          else
            ergo_format_clause_return_component_error
              nsctxt name "fail with" "fails with" actual_error expected_error
        else
          ergo_format_clause_return_component_error
            nsctxt name "set state" "sets state" actual_state expected_state
      else
        ergo_format_clause_return_component_error
          nsctxt name "emit" "emits" actual_emit expected_emit
    else
      ergo_format_clause_return_component_error
        nsctxt name "respond" "responds" actual_resp expected_resp.

  Definition ergo_format_clause_return_error nsctxt (name:string) (actual expected:ergoc_type) : string :=
    let actual_quad := unpack_output_type nsctxt actual nil in
    let expected_quad := unpack_output_type nsctxt expected nil in
    let normal_error := ergo_format_clause_return_normal_error nsctxt name actual expected in
    let fallback_error := fun e => ergo_format_clause_return_fallback_error nsctxt name actual expected in
    elift2_both
      normal_error
      fallback_error
      actual_quad
      expected_quad.
  
  Definition ergo_format_function_return_error nsctxt (name:string) (actual expected:ergoc_type) : string :=
    let actual_s := ergoc_type_to_string nsctxt actual in
    let expected_s := ergoc_type_to_string nsctxt expected in
    "Function " ++ name ++ " should return `" ++ expected_s ++ "' but actually returns `" ++ actual_s ++ "'".

  Definition make_unary_operator_criteria op nsctxt prov t : eresult ergoc_type :=
    match ergoc_type_infer_unary_op op t with
    | Some (r, _) => esuccess r nil
    | None => efailure (ETypeError prov (ergo_format_unop_error nsctxt op t))
    end.

  Definition make_binary_operator_criteria op nsctxt prov t1 t2 : eresult ergoc_type :=
    match ergoc_type_infer_binary_op op t1 t2 with
    | Some (r, _, _) => esuccess r nil
    | None => efailure (ETypeError prov (ergo_format_binop_error nsctxt op t1 t2))
    end.

End ErgoCTypeUtil.
