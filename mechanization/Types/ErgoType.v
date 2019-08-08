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

Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.

Section ErgoType.
  Section Ast.
    Context {A:Set}. (* Type for annotations *)
    Context {N:Set}. (* Type for names *)
  
    Inductive ergo_type :=
    | ErgoTypeAny : A -> ergo_type                               (**r any type *)
    | ErgoTypeNothing : A -> ergo_type                           (**r nothing type *)
    | ErgoTypeUnit : A -> ergo_type                              (**r unit type *)
    | ErgoTypeBoolean : A -> ergo_type                           (**r bool atomic type *)
    | ErgoTypeString : A -> ergo_type                            (**r string atomic type *)
    | ErgoTypeDouble : A -> ergo_type                            (**r double atomic type *)
    | ErgoTypeLong : A -> ergo_type                              (**r long atomic type *)
    | ErgoTypeInteger : A -> ergo_type                           (**r integer atomic type *)
    | ErgoTypeDateTimeFormat : A -> ergo_type                    (**r date and time atomic type *)
    | ErgoTypeDateTime : A -> ergo_type                          (**r date and time atomic type *)
    | ErgoTypeDuration : A -> ergo_type                          (**r duration atomic type *)
    | ErgoTypePeriod : A -> ergo_type                            (**r period atomic type *)
    | ErgoTypeClassRef : A -> N -> ergo_type                     (**r relative class reference *)
    | ErgoTypeOption : A -> ergo_type -> ergo_type               (**r optional type *)
    | ErgoTypeRecord : A -> list (string*ergo_type) -> ergo_type (**r record type *)
    | ErgoTypeArray : A -> ergo_type -> ergo_type                (**r array type *)
    | ErgoTypeSum : A -> ergo_type -> ergo_type -> ergo_type     (**r sum type *)
    .

    Definition type_annot (et:ergo_type) : A :=
      match et with
      | ErgoTypeAny a => a
      | ErgoTypeNothing a => a
      | ErgoTypeUnit a => a
      | ErgoTypeBoolean a => a
      | ErgoTypeString a => a
      | ErgoTypeDouble a => a
      | ErgoTypeLong a => a
      | ErgoTypeInteger a => a
      | ErgoTypeDateTimeFormat a => a
      | ErgoTypeDateTime a => a
      | ErgoTypeDuration a => a
      | ErgoTypePeriod a => a
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
          type_signature_output : option ergo_type;
          type_signature_emits  : option ergo_type; }.

    Inductive ergo_type_declaration_desc :=
    | ErgoTypeEnum : list string -> ergo_type_declaration_desc
    | ErgoTypeTransaction : is_abstract -> @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeConcept : is_abstract -> @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeEvent : is_abstract -> @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeAsset : is_abstract -> @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
    | ErgoTypeParticipant : is_abstract -> @extends N -> list (string * ergo_type) -> ergo_type_declaration_desc
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

    Section Abstract.
      Definition type_declaration_is_abstract
                 (decl_desc:ergo_type_declaration_desc) : is_abstract :=
        match decl_desc with
        | ErgoTypeEnum _ => false
        | ErgoTypeTransaction isabs _ _ => isabs
        | ErgoTypeConcept isabs _ _ => isabs
        | ErgoTypeEvent isabs _ _ => isabs
        | ErgoTypeAsset isabs _ _ => isabs
        | ErgoTypeParticipant isabs _ _ => isabs
        | ErgoTypeGlobal _ => false
        | ErgoTypeFunction _ => false
        | ErgoTypeContract _ _ _ => false
        end.

    End Abstract.

    Section Enum.
      Definition type_declaration_is_enum
                 (d:ergo_type_declaration_desc)
      : option (list string) :=
        match d with
        | ErgoTypeEnum enum_list => Some enum_list
        | _ => None
        end.

  End Enum.
  
  End Ast.

  Definition rergo_type {A} : Set := @ergo_type A relative_name.
  Definition rergo_type_signature {A} : Set := @ergo_type_signature A relative_name.
  Definition rergo_type_declaration {A} : Set := @ergo_type_declaration A relative_name.
  Definition rergo_type_declaration_desc {A} : Set := @ergo_type_declaration_desc A relative_name.

  Definition aergo_type {A} : Set := @ergo_type A absolute_name.
  Definition aergo_type_signature {A} : Set := @ergo_type_signature A absolute_name.
  Definition aergo_type_declaration_desc {A} : Set := @ergo_type_declaration_desc A absolute_name.
  Definition aergo_type_declaration {A} : Set := @ergo_type_declaration A absolute_name.
  
  Definition lrergo_type : Set := @ergo_type provenance relative_name.
  Definition lrergo_type_signature : Set := @ergo_type_signature provenance relative_name.
  Definition lrergo_type_declaration_desc : Set := @ergo_type_declaration_desc provenance relative_name.
  Definition lrergo_type_declaration : Set := @ergo_type_declaration provenance relative_name.

  Definition laergo_type : Set := @ergo_type provenance absolute_name.
  Definition laergo_type_signature : Set := @ergo_type_signature provenance absolute_name.
  Definition laergo_type_declaration : Set := @ergo_type_declaration provenance absolute_name.
  Definition laergo_type_declaration_desc : Set := @ergo_type_declaration_desc provenance absolute_name.
  
  Definition lift_default_emits_type (prov:provenance) (emits:option laergo_type) : laergo_type :=
    match emits with
    | Some e => e
    | None => ErgoTypeClassRef prov default_event_absolute_name
    end.

  Definition lift_default_state_type (prov:provenance) (state:option laergo_type) : laergo_type :=
    match state with
    | Some e => e
    | None => ErgoTypeClassRef prov default_state_absolute_name
    end.

  Definition default_throws_type (prov:provenance) : laergo_type :=
    ErgoTypeClassRef prov default_error_absolute_name.

  Definition mk_success_type (prov:provenance) (response_type state_type emit_type: laergo_type) : laergo_type :=
    ErgoTypeRecord prov
       ((this_response,response_type)
          ::(this_state,state_type)
          ::(this_emit,ErgoTypeArray prov emit_type)
          ::nil)%string.

  Definition mk_error_type (prov:provenance) (throw_type: laergo_type) : laergo_type := throw_type.
  Definition mk_output_type (prov:provenance) (success_type error_type: laergo_type) : laergo_type :=
    ErgoTypeSum prov success_type error_type.

  Definition lift_default_state_name (state:option laergo_type) : eresult absolute_name :=
    match state with
    | None => esuccess default_state_absolute_name nil
    | Some et =>
      match et with
      | ErgoTypeClassRef _ r => esuccess r nil
      | _ => unresolved_name_error (type_annot et)
      end
    end.

  Section Extends.
    Definition fix_nothing (to:absolute_name) : list (absolute_name * absolute_name) := nil.
    Definition fix_transaction (to:absolute_name) :=
      if string_dec to default_transaction_absolute_name
      then nil
      else (to, default_transaction_absolute_name) :: nil.
    Definition fix_event (to:absolute_name) :=
      if string_dec to default_event_absolute_name
      then nil
      else (to, default_event_absolute_name) :: nil.
    Definition fix_asset (to:absolute_name) :=
      if string_dec to default_asset_absolute_name
      then nil
      else (to, default_asset_absolute_name) :: nil.
    Definition fix_participant (to:absolute_name) :=
      if string_dec to default_participant_absolute_name
      then nil
      else (to, default_participant_absolute_name) :: nil.
    
    Definition extends_rel
               (fix_none:absolute_name -> list (absolute_name * absolute_name))
               (to:absolute_name)
               (e:@extends absolute_name) : list (absolute_name * absolute_name) :=
      match e with
      | None => fix_none to
      | Some from => (to,from) :: nil
      end.

    Definition type_declaration_desc_extend_rel
               (to:absolute_name)
               (decl_desc:laergo_type_declaration_desc) : list (absolute_name * absolute_name) :=
      match decl_desc with
      | ErgoTypeEnum _ => extends_rel fix_nothing to None
      | ErgoTypeTransaction _ e _ => extends_rel fix_transaction to e
      | ErgoTypeConcept _ e _ => extends_rel fix_nothing to e
      | ErgoTypeEvent _ e _ => extends_rel fix_event to e
      | ErgoTypeAsset _ e _ => extends_rel fix_asset to e
      | ErgoTypeParticipant _ e _ => extends_rel fix_participant to e
      | ErgoTypeGlobal _ => nil
      | ErgoTypeFunction _ => nil
      | ErgoTypeContract _ _ _ => extends_rel fix_nothing to None
      end.

    Definition type_declaration_extend_rel
               (decl:laergo_type_declaration) : list (absolute_name * absolute_name) :=
      type_declaration_desc_extend_rel decl.(type_declaration_name) decl.(type_declaration_type).

    Definition type_declarations_extend_rel
               (decls:list laergo_type_declaration) : list (absolute_name * absolute_name) :=
      List.concat (List.map type_declaration_extend_rel decls).
  End Extends.
  
End ErgoType.
