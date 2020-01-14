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

val ergo_expand_class_object_extends :
  expand_ctxt -> absolute_name -> absolute_name -> (char list * laergo_type)
  list -> expand_ctxt

val ergo_expand_class_enum_extends :
  expand_ctxt -> absolute_name -> absolute_name -> char list list ->
  expand_ctxt

val ergo_decl_expand_extends :
  expand_ctxt -> absolute_name -> laergo_type_declaration_desc -> expand_ctxt

val ergo_expand_extends_in_declarations :
  laergo_type_declaration list -> expand_ctxt

val ergo_hierarchy_from_expand : expand_ctxt -> (char list * char list) list

val ergo_type_to_qcert_type : brand_relation -> laergo_type -> qcert_type

val enum_type_of_list : brand_relation -> char list list -> qcert_type

val ergo_ctype_from_expanded_type :
  brand_relation -> expanded_type -> qcert_type

val ergo_ctype_decl_from_expand :
  brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls

val brand_relation_maybe :
  (char list * char list) list -> QcertType.tbrand_relation eresult

val mk_model_type_decls :
  brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls

val brand_model_of_declarations :
  laergo_type_declaration list ->
  (QcertType.tbrand_model * laergo_type_declaration list) eresult
