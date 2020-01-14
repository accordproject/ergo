open Assoc
open Bindings
open BrandRelation
open Datatypes
open ErgoType
open List0
open Names
open Provenance
open QLib
open Result0
open String0

type expand_hierarchy = char list list

type expanded_type =
| ClassObjectType of (char list * laergo_type) list
| ClassEnumType of char list list

type expand_ctxt = (char list * (expand_hierarchy * expanded_type)) list

(** val ergo_expand_class_object_extends :
    expand_ctxt -> absolute_name -> absolute_name ->
    (char list * laergo_type) list -> expand_ctxt **)

let ergo_expand_class_object_extends ctxt this super localtype =
  match lookup string_dec ctxt super with
  | Some p ->
    let (hierarchy, e) = p in
    (match e with
     | ClassObjectType etype ->
       (this, ((super :: hierarchy), (ClassObjectType
         (app etype localtype)))) :: ctxt
     | ClassEnumType _ -> ctxt)
  | None -> ctxt

(** val ergo_expand_class_enum_extends :
    expand_ctxt -> absolute_name -> absolute_name -> char list list ->
    expand_ctxt **)

let ergo_expand_class_enum_extends ctxt this super enum_list =
  (this, ((super :: []), (ClassEnumType enum_list))) :: ctxt

(** val ergo_decl_expand_extends :
    expand_ctxt -> absolute_name -> laergo_type_declaration_desc ->
    expand_ctxt **)

let ergo_decl_expand_extends ctxt this = function
| ErgoTypeEnum enum_list ->
  ergo_expand_class_enum_extends ctxt this default_enum_absolute_name
    enum_list
| ErgoTypeTransaction (_, e, rtl) ->
  (match e with
   | Some super -> ergo_expand_class_object_extends ctxt this super rtl
   | None ->
     if string_dec this default_transaction_absolute_name
     then (this, ([], (ClassObjectType rtl))) :: ctxt
     else ergo_expand_class_object_extends ctxt this
            default_transaction_absolute_name rtl)
| ErgoTypeConcept (_, e, rtl) ->
  (match e with
   | Some super -> ergo_expand_class_object_extends ctxt this super rtl
   | None -> (this, ([], (ClassObjectType rtl))) :: ctxt)
| ErgoTypeEvent (_, e, rtl) ->
  (match e with
   | Some super -> ergo_expand_class_object_extends ctxt this super rtl
   | None ->
     if string_dec this default_event_absolute_name
     then (this, ([], (ClassObjectType rtl))) :: ctxt
     else ergo_expand_class_object_extends ctxt this
            default_event_absolute_name rtl)
| ErgoTypeAsset (_, e, rtl) ->
  (match e with
   | Some super -> ergo_expand_class_object_extends ctxt this super rtl
   | None ->
     if string_dec this default_asset_absolute_name
     then (this, ([], (ClassObjectType rtl))) :: ctxt
     else ergo_expand_class_object_extends ctxt this
            default_asset_absolute_name rtl)
| ErgoTypeParticipant (_, e, rtl) ->
  (match e with
   | Some super -> ergo_expand_class_object_extends ctxt this super rtl
   | None ->
     if string_dec this default_participant_absolute_name
     then (this, ([], (ClassObjectType rtl))) :: ctxt
     else ergo_expand_class_object_extends ctxt this
            default_participant_absolute_name rtl)
| _ -> ctxt

(** val ergo_expand_extends_in_declarations :
    laergo_type_declaration list -> expand_ctxt **)

let ergo_expand_extends_in_declarations decls =
  fold_left (fun ctxt decl ->
    ergo_decl_expand_extends ctxt decl.type_declaration_name
      decl.type_declaration_type) decls []

(** val ergo_hierarchy_from_expand :
    expand_ctxt -> (char list * char list) list **)

let ergo_hierarchy_from_expand ctxt =
  List0.concat
    (map (fun xyz ->
      let (super, y) = xyz in
      let (hierarchy, _) = y in map (fun x -> (super, x)) hierarchy) ctxt)

(** val ergo_type_to_qcert_type :
    brand_relation -> laergo_type -> qcert_type **)

let rec ergo_type_to_qcert_type m = function
| ErgoTypeAny _ -> QcertType.ttop m
| ErgoTypeNothing _ -> QcertType.tbottom m
| ErgoTypeUnit _ -> QcertType.tunit m
| ErgoTypeBoolean _ -> QcertType.tbool m
| ErgoTypeString _ -> QcertType.tstring m
| ErgoTypeDouble _ -> QcertType.tfloat m
| ErgoTypeDateTimeFormat _ -> QcertType.tdateTimeFormat m
| ErgoTypeDateTime _ -> QcertType.tdateTime m
| ErgoTypeDuration _ -> QcertType.tduration m
| ErgoTypePeriod _ -> QcertType.tperiod m
| ErgoTypeClassRef (_, cr) -> QcertType.tbrand m (cr :: [])
| ErgoTypeOption (_, t0) ->
  QcertType.teither m (ergo_type_to_qcert_type m t0) (QcertType.tunit m)
| ErgoTypeRecord (_, rtl) ->
  QcertType.trec m QcertType.open_kind
    (rec_sort coq_ODT_string
      (map (fun xy -> ((fst xy), (ergo_type_to_qcert_type m (snd xy)))) rtl))
| ErgoTypeArray (_, t0) -> QcertType.tcoll m (ergo_type_to_qcert_type m t0)
| ErgoTypeSum (_, t1, t2) ->
  QcertType.teither m (ergo_type_to_qcert_type m t1)
    (ergo_type_to_qcert_type m t2)
| _ -> QcertType.tnat m

(** val enum_type_of_list : brand_relation -> char list list -> qcert_type **)

let rec enum_type_of_list m = function
| [] -> QcertType.tstring m
| _ :: enum_list' ->
  QcertType.teither m (QcertType.tstring m) (enum_type_of_list m enum_list')

(** val ergo_ctype_from_expanded_type :
    brand_relation -> expanded_type -> qcert_type **)

let ergo_ctype_from_expanded_type m = function
| ClassObjectType rtl ->
  QcertType.trec m QcertType.open_kind
    (rec_sort coq_ODT_string
      (map (fun xy -> ((fst xy), (ergo_type_to_qcert_type m (snd xy)))) rtl))
| ClassEnumType enum_list -> enum_type_of_list m enum_list

(** val ergo_ctype_decl_from_expand :
    brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls **)

let ergo_ctype_decl_from_expand m ctxt =
  (default_enum_absolute_name,
    (QcertType.ttop m)) :: (map (fun xyz -> ((fst xyz),
                             (let expanded = snd (snd xyz) in
                              ergo_ctype_from_expanded_type m expanded)))
                             ctxt)

(** val brand_relation_maybe :
    (char list * char list) list -> QcertType.tbrand_relation eresult **)

let brand_relation_maybe hierarchy =
  eresult_of_qresult dummy_provenance (QcertType.mk_tbrand_relation hierarchy)

(** val mk_model_type_decls :
    brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls **)

let mk_model_type_decls =
  ergo_ctype_decl_from_expand

(** val brand_model_of_declarations :
    laergo_type_declaration list ->
    (QcertType.tbrand_model * laergo_type_declaration list) eresult **)

let brand_model_of_declarations decls =
  let decls0 = sort_decls decls in
  let ctxt = ergo_expand_extends_in_declarations decls0 in
  let hierarchy = ergo_hierarchy_from_expand ctxt in
  let res =
    eolift (fun br ->
      eresult_of_qresult dummy_provenance
        (QcertType.mk_tbrand_model br (mk_model_type_decls br ctxt)))
      (brand_relation_maybe hierarchy)
  in
  elift (fun x -> (x, decls0)) res
