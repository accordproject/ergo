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

Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoTypeExpansion.
  Definition expand_hierarchy : Set := list string.
  Definition expanded_type : Set := list (string * laergo_type).
  Definition expand_ctxt : Set := list (string * (expand_hierarchy * expanded_type)).

  (** Assumes decls sorted in topological order *)
  Definition ergo_expand_extends
             (ctxt:expand_ctxt)
             (this:absolute_name)
             (super:absolute_name)
             (localtype:list (string * laergo_type)) : expand_ctxt :=
    match lookup string_dec ctxt super with
    | None => ctxt (** XXX Should be a system error *)
    | Some (hierarchy, etype) =>
      (this, (super::hierarchy,etype ++ localtype)) :: ctxt
    end.

  Definition ergo_decl_expand_extends (ctxt:expand_ctxt)
             (this:absolute_name)
             (decl_desc:laergo_type_declaration_desc) : expand_ctxt :=
    match decl_desc with
    | ErgoTypeEnum _ => ctxt
    | ErgoTypeTransaction e _ => ctxt
    | ErgoTypeConcept None rtl =>
      (this, (nil, rtl)) :: ctxt
    | ErgoTypeConcept (Some super) rtl =>
      ergo_expand_extends ctxt this super rtl
    | ErgoTypeEvent e _ => ctxt
    | ErgoTypeAsset e _ => ctxt
    | ErgoTypeParticipant e _ => ctxt
    | ErgoTypeGlobal _ => ctxt
    | ErgoTypeFunction _ => ctxt
    | ErgoTypeContract _ _ _ => ctxt
    end.

  Fixpoint ergo_expand_extends_in_declarations (decls:list laergo_type_declaration) : expand_ctxt :=
    List.fold_left
      (fun ctxt decl =>
         ergo_decl_expand_extends
           ctxt
           decl.(type_declaration_name)
           decl.(type_declaration_type))
      decls nil.

  Definition ergo_hierarchy_from_expand (ctxt : expand_ctxt) :=
    List.concat
      (List.map (fun xyz =>
                   List.map (fun x => (fst xyz, x)) (fst (snd xyz)))
                ctxt).

End ErgoTypeExpansion.

Section ErgoTypetoErgoCType.
  Context {m:brand_relation}.
  Import ErgoCTypes.

  Fixpoint ergo_type_to_ergoc_type (t:laergo_type) : ergoc_type :=
    match t with
    | ErgoTypeAny _ => ttop
    | ErgoTypeNone _ => tbottom
    | ErgoTypeBoolean _ => tbool
    | ErgoTypeString _ => tstring
    | ErgoTypeDouble _ => tfloat
    | ErgoTypeLong _ => tfloat
    | ErgoTypeInteger _ => tnat
    | ErgoTypeDateTime _ => tbottom
    | ErgoTypeClassRef _ cr => tbrand (cr::nil)
    | ErgoTypeOption _ t => teither (ergo_type_to_ergoc_type t) tunit
    | ErgoTypeRecord _ rtl =>
      trec
        open_kind
        (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
        (rec_sort_sorted
           (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl)
           (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
           eq_refl)
    | ErgoTypeArray _ t => tcoll (ergo_type_to_ergoc_type t)
    | ErgoTypeSum _ t1 t2 => teither (ergo_type_to_ergoc_type t1) (ergo_type_to_ergoc_type t2)
    end.

  Definition ergo_ctype_decl_from_expand (ctxt : expand_ctxt) : tbrand_context_decls :=
    List.map (fun xyz =>
                (fst xyz,
                 let rtl := snd (snd xyz) in
                 trec
                   open_kind
                   (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
                   (rec_sort_sorted
                      (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl)
                      (rec_sort (List.map (fun xy => (fst xy, ergo_type_to_ergoc_type (snd xy))) rtl))
                      eq_refl))) ctxt.

End ErgoTypetoErgoCType.

Section TestModel.
  Import ErgoCTypes.

  Local Open Scope string.

  (* For the CTO:
     ============

     concept Entity {}
     concept Customer extends Entity { o Integer age o Integer cid o String name }
     concept Purchase extends Entity { o Integer cid o String name o Integer pid o Integer quantity }
   *)

  Definition StoreHierarchy :=
    ("org.accordproject.ergotop.Customer","org.accordproject.ergotop.Entity")::("org.accordproject.ergotop.Purchase","org.accordproject.ergotop.Entity")::nil.

  Definition StoreBrandRelationMaybe : eresult tbrand_relation
    := eresult_of_qresult dummy_provenance (mk_tbrand_relation StoreHierarchy).

  Definition StoreBrandRelation : brand_relation :=
    match StoreBrandRelationMaybe with
    | Success _ _ s => s
    | Failure _ _ e => tempty_brand_relation (* Not used *)
    end.

  (* Compute StoreBrandModelMaybe. *)
  
  Existing Instance StoreBrandRelation.

  Program Definition EntityType : ergoc_type
    := Rec Open nil _.

  Program Definition CustomerType : ergoc_type
    := Rec Open (("age", Nat)
                 :: ("cid", Nat)
                 :: ("name", String)
                 :: nil) _.

  Program Definition PurchaseType : ergoc_type
    := Rec Open (("cid", Nat)
                 :: ("name", String)
                 :: ("pid", Nat)
                 :: ("quantity", Nat)
                 :: nil) _.

  Definition StoreModelTypeDecls : tbrand_context_decls :=
    (("org.accordproject.ergotop.Customer", CustomerType)
     :: ("org.accordproject.ergotop.Entity", EntityType)
     :: ("org.accordproject.ergotop.Purchase", PurchaseType)
     :: nil).

  Definition StoreBrandModelMaybe : eresult tbrand_model
    := eresult_of_qresult dummy_provenance
                          (mk_tbrand_model StoreModelTypeDecls).

  (* Compute StoreBrandModelMaybe. *)
  
  Instance StoreBrandModel : brand_model :=
    match StoreBrandModelMaybe with
    | Success _ _ s => s
    | Failure _ _ e => tempty_brand_model (* Not used *)
    end.

End TestModel.

Section Translate.
  Local Open Scope string.
  Import ErgoCTypes.

  Definition EntityDecl : laergo_type_declaration :=
    mkErgoTypeDeclaration dummy_provenance "org.accordproject.ergotop.Entity"
                          (ErgoTypeConcept None nil).
  Definition CustomerDecl : laergo_type_declaration :=
    mkErgoTypeDeclaration dummy_provenance "org.accordproject.ergotop.Customer"
                          (ErgoTypeConcept (Some "org.accordproject.ergotop.Entity")
                                           (("age",ErgoTypeInteger dummy_provenance)
                                              ::("cid",ErgoTypeInteger dummy_provenance)
                                              ::("name",ErgoTypeString dummy_provenance)
                                              ::nil)).
  Definition GoldCustomerDecl : laergo_type_declaration :=
    mkErgoTypeDeclaration dummy_provenance "org.accordproject.ergotop.GoldCustomer"
                          (ErgoTypeConcept (Some "org.accordproject.ergotop.Customer")
                                           (("status",ErgoTypeString dummy_provenance)
                                              ::nil)).
  Definition PurchaseDecl : laergo_type_declaration :=
    mkErgoTypeDeclaration dummy_provenance "org.accordproject.ergotop.Purchase"
                          (ErgoTypeConcept (Some "org.accordproject.ergotop.Entity")
                                           (("cid",ErgoTypeInteger dummy_provenance)
                                              :: ("name",ErgoTypeString dummy_provenance)
                                              :: ("pid",ErgoTypeInteger dummy_provenance)
                                              :: ("quantity",ErgoTypeInteger dummy_provenance)
                                              ::nil)).
  Definition BearDecl : laergo_type_declaration :=
    mkErgoTypeDeclaration dummy_provenance "org.accordproject.ergotop.Bear"
                          (ErgoTypeConcept (Some "org.accordproject.ergotop.Entity")
                                           (("name",ErgoTypeString dummy_provenance)
                                              :: ("age",ErgoTypeInteger dummy_provenance)
                                              ::nil)).
  Definition StoreDecls : list laergo_type_declaration :=
    EntityDecl :: CustomerDecl :: PurchaseDecl :: (* GoldCustomerDecl :: *) BearDecl :: nil. 
  
  (* Compute (hierarchy StoreDecls). *)
  
  Definition brand_relation_maybe hierarchy : eresult tbrand_relation
    := eresult_of_qresult dummy_provenance (mk_tbrand_relation hierarchy).

  (* Compute (brand_relation_maybe StoreDecls). *)

  Definition mk_model_type_decls {br:brand_relation} (ctxt : expand_ctxt) : tbrand_context_decls :=
    @ergo_ctype_decl_from_expand br ctxt.

  Definition brand_model_of_declarations (decls:list laergo_type_declaration)
    : eresult ErgoCTypes.tbrand_model :=
    let ctxt := ergo_expand_extends_in_declarations decls in
    let hierarchy := ergo_hierarchy_from_expand ctxt in
    eolift (fun br =>
              eresult_of_qresult dummy_provenance
                                 (mk_tbrand_model (@mk_model_type_decls br ctxt)))
           (brand_relation_maybe hierarchy).
  
  Definition force_brand_model_of_declarations (decls:list laergo_type_declaration)
    : ErgoCTypes.tbrand_model :=
    match brand_model_of_declarations decls with
    | Success _ _ s => s
    | Failure _ _ e => tempty_brand_model (* Not used *)
    end.

  (* Compute brand_model_of_declarations StoreDecls. *)

End Translate.

