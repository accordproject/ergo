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
Require Import ErgoSpec.Common.Utils.EImport.

Section ErgoType.

  Inductive ergo_type_desc :=
  | ErgoTypeAny : ergo_type_desc                               (**r any type *)
  | ErgoTypeNone : ergo_type_desc                              (**r none type *)
  | ErgoTypeBoolean : ergo_type_desc                           (**r bool atomic type *)
  | ErgoTypeString : ergo_type_desc                            (**r string atomic type *)
  | ErgoTypeDouble : ergo_type_desc                            (**r double atomic type *)
  | ErgoTypeLong : ergo_type_desc                              (**r long atomic type *)
  | ErgoTypeInteger : ergo_type_desc                           (**r integer atomic type *)
  | ErgoTypeDateTime : ergo_type_desc                          (**r date and time atomic type *)
  | ErgoTypeClassRef : name_ref -> ergo_type_desc              (**r relative class reference *)
  | ErgoTypeOption : ergo_type -> ergo_type_desc               (**r optional type *)
  | ErgoTypeRecord : list (string*ergo_type) -> ergo_type_desc (**r record type *)
  | ErgoTypeArray : ergo_type -> ergo_type_desc                (**r array type *)
  | ErgoTypeSum : ergo_type -> ergo_type -> ergo_type_desc     (**r sum type *)
  with ergo_type :=
  | ErgoType : location -> ergo_type_desc -> ergo_type.

  Definition type_loc (et:ergo_type) : location :=
    match et with
    | ErgoType loc _ => loc
    end.
  Definition type_desc (et:ergo_type) : ergo_type_desc :=
    match et with
    | ErgoType _ etd => etd
   end.
  Definition mk_type (loc:location) (etd:ergo_type_desc) : ergo_type :=
    ErgoType loc etd.

  Record ergo_type_signature : Set :=
    mkErgoTypeSignature
      { type_signature_name: string;
        type_signature_location : location;
        type_signature_params : list (string * ergo_type);
        type_signature_output : ergo_type;
        type_signature_throws : option ergo_type;
        type_signature_emits : option ergo_type; }.

  Inductive ergo_type_declaration_desc :=
  | ErgoTypeEnum : list string -> ergo_type_declaration_desc
  | ErgoTypeTransaction : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_desc
  | ErgoTypeConcept : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_desc
  | ErgoTypeEvent : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_desc
  | ErgoTypeAsset : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_desc
  | ErgoTypeParticipant : option name_ref -> list (string * ergo_type) -> ergo_type_declaration_desc
  | ErgoTypeGlobal : ergo_type -> ergo_type_declaration_desc
  | ErgoTypeFunction : ergo_type_signature -> ergo_type_declaration_desc
  | ErgoTypeContract :
      ergo_type                              (**r template type *)
      -> ergo_type                           (**r state type *)
      -> list (string * ergo_type_signature) (**r clauses signatures *)
      -> ergo_type_declaration_desc.

  Record ergo_type_declaration :=
    mkErgoTypeDeclaration
      { type_declaration_name : local_name;
        type_declaration_location : location;
        type_declaration_type : ergo_type_declaration_desc; }.

  Record ergo_type_module :=
    mkErgoTypeModule
      { type_module_namespace : namespace_name;
        type_module_location : location;
        type_module_imports : list import_decl;
        type_module_declarations : list ergo_type_declaration; }.

  Definition lift_default_emits_type (loc:location) (emits:option ergo_type) : ergo_type :=
    match emits with
    | Some e => e
    | None => mk_type loc (ErgoTypeClassRef default_emits_type)
    end.

  Definition lift_default_state_type (loc:location) (state:option ergo_type) : ergo_type :=
    match state with
    | Some e => e
    | None => mk_type loc (ErgoTypeClassRef default_state_type)
    end.

  Definition lift_default_throws_type (loc:location) (emits:option ergo_type) : ergo_type :=
    match emits with
    | Some e => e
    | None => mk_type loc (ErgoTypeClassRef default_throws_type)
    end.

  Definition mk_success_type (loc:location) (response_type state_type emit_type: ergo_type) :=
    mk_type loc
            (ErgoTypeRecord
               (("response",response_type)
                  ::("state",state_type)
                  ::("emit",emit_type)
                  ::nil))%string.
  Definition mk_error_type (loc:location) (throw_type: ergo_type) := throw_type.
  Definition mk_output_type (loc:location) (success_type error_type: ergo_type) :=
    mk_type loc (ErgoTypeSum success_type error_type).

  Definition lift_default_state_name (state:option ergo_type) : eresult absolute_name :=
    match state with
    | None => esuccess default_state_name
    | Some et =>
      match type_desc et with
      | (ErgoTypeClassRef (AbsoluteRef r)) => esuccess r
      | _ => unresolved_name_error (type_loc et)
      end
    end.
  
End ErgoType.
