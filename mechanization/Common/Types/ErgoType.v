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
Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.TypingRuntime.

Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EAstUtil.

Section ErgoType.
  Section Ast.
    Context {A:Set}. (* Type for annotations *)
    Context {N:Set}. (* Type for names *)
  
    Inductive ergo_type :=
    | ErgoTypeAny : A -> ergo_type                               (**r any type *)
    | ErgoTypeNone : A -> ergo_type                              (**r none type *)
    | ErgoTypeBoolean : A -> ergo_type                           (**r bool atomic type *)
    | ErgoTypeString : A -> ergo_type                            (**r string atomic type *)
    | ErgoTypeDouble : A -> ergo_type                            (**r double atomic type *)
    | ErgoTypeLong : A -> ergo_type                              (**r long atomic type *)
    | ErgoTypeInteger : A -> ergo_type                           (**r integer atomic type *)
    | ErgoTypeDateTime : A -> ergo_type                          (**r date and time atomic type *)
    | ErgoTypeClassRef : A -> N -> ergo_type                     (**r relative class reference *)
    | ErgoTypeOption : A -> ergo_type -> ergo_type               (**r optional type *)
    | ErgoTypeRecord : A -> list (string*ergo_type) -> ergo_type (**r record type *)
    | ErgoTypeArray : A -> ergo_type -> ergo_type                (**r array type *)
    | ErgoTypeSum : A -> ergo_type -> ergo_type -> ergo_type     (**r sum type *)
    .

    Definition type_annot (et:ergo_type) : A :=
      match et with
      | ErgoTypeAny a => a
      | ErgoTypeNone a => a
      | ErgoTypeBoolean a => a
      | ErgoTypeString a => a
      | ErgoTypeDouble a => a
      | ErgoTypeLong a => a
      | ErgoTypeInteger a => a
      | ErgoTypeDateTime a => a
      | ErgoTypeClassRef a _ => a
      | ErgoTypeOption a _ => a
      | ErgoTypeRecord a _ => a
      | ErgoTypeArray a _ => a
      | ErgoTypeSum a _ _ => a
      end.

    Record ergo_type_signature : Set :=
      mkErgoTypeSignature
        { type_signature_annot : A;
          type_signature_params : list (string * ergo_type);
          type_signature_output : ergo_type;
          type_signature_throws : option ergo_type;
          type_signature_emits : option ergo_type; }.

    Inductive ergo_type_declaration_desc :=
    | ErgoTypeEnum : list string -> ergo_type_declaration_desc
    | ErgoTypeTransaction : @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeConcept : @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeEvent : @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeAsset : @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeParticipant : @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeGlobal : ergo_type -> ergo_type_declaration_desc
    | ErgoTypeFunction : ergo_type_signature -> ergo_type_declaration_desc
    | ErgoTypeContract :
        ergo_type                              (**r template type *)
        -> ergo_type                           (**r state type *)
        -> list (string * ergo_type_signature) (**r clauses signatures *)
        -> ergo_type_declaration_desc.

    Record ergo_type_declaration :=
      mkErgoTypeDeclaration
        { type_declaration_annot : A;
          type_declaration_name : local_name;
          type_declaration_type : ergo_type_declaration_desc; }.

  End Ast.

  Definition rergo_type {A} : Set := @ergo_type A relative_name.
  Definition rergo_type_signature {A} : Set := @ergo_type_signature A relative_name.
  Definition rergo_type_declaration {A} : Set := @ergo_type_declaration A relative_name.
  Definition rergo_type_declaration_desc {A} : Set := @ergo_type_declaration_desc A relative_name.

  Definition aergo_type {A} : Set := @ergo_type A absolute_name.
  Definition aergo_type_signature {A} : Set := @ergo_type_signature A absolute_name.
  Definition aergo_type_declaration_desc {A} : Set := @ergo_type_declaration_desc A absolute_name.
  Definition aergo_type_declaration {A} : Set := @ergo_type_declaration A absolute_name.
  
  Definition lrergo_type : Set := @ergo_type location relative_name.
  Definition lrergo_type_signature : Set := @ergo_type_signature location relative_name.
  Definition lrergo_type_declaration_desc : Set := @ergo_type_declaration_desc location relative_name.
  Definition lrergo_type_declaration : Set := @ergo_type_declaration location relative_name.

  Definition laergo_type : Set := @ergo_type location absolute_name.
  Definition laergo_type_signature : Set := @ergo_type_signature location absolute_name.
  Definition laergo_type_declaration : Set := @ergo_type_declaration location absolute_name.
  Definition laergo_type_declaration_desc : Set := @ergo_type_declaration_desc location absolute_name.
  
  Definition lift_default_emits_type (loc:location) (emits:option laergo_type) : laergo_type :=
    match emits with
    | Some e => e
    | None => ErgoTypeClassRef loc default_emits_absolute_name
    end.

  Definition lift_default_state_type (loc:location) (state:option laergo_type) : laergo_type :=
    match state with
    | Some e => e
    | None => ErgoTypeClassRef loc default_state_absolute_name
    end.

  Definition lift_default_throws_type (loc:location) (emits:option laergo_type) : laergo_type :=
    match emits with
    | Some e => e
    | None => ErgoTypeClassRef loc default_throws_absolute_name
    end.

  Definition mk_success_type (loc:location) (response_type state_type emit_type: laergo_type) : laergo_type :=
    ErgoTypeRecord loc
       (("response",response_type)
          ::("state",state_type)
          ::("emit",emit_type)
          ::nil)%string.

  Definition mk_error_type (loc:location) (throw_type: laergo_type) : laergo_type := throw_type.
  Definition mk_output_type (loc:location) (success_type error_type: laergo_type) : laergo_type :=
    ErgoTypeSum loc success_type error_type.

  Definition lift_default_state_name (state:option laergo_type) : eresult absolute_name :=
    match state with
    | None => esuccess default_state_absolute_name
    | Some et =>
      match et with
      | ErgoTypeClassRef _ r => esuccess r
      | _ => unresolved_name_error (type_annot et)
      end
    end.

End ErgoType.
