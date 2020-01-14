open Assoc
open Ast
open Datatypes
open List0
open Misc
open Names
open Provenance
open String0

type ('a, 'n) ergo_type =
| ErgoTypeAny of 'a
| ErgoTypeNothing of 'a
| ErgoTypeUnit of 'a
| ErgoTypeBoolean of 'a
| ErgoTypeString of 'a
| ErgoTypeDouble of 'a
| ErgoTypeLong of 'a
| ErgoTypeInteger of 'a
| ErgoTypeDateTimeFormat of 'a
| ErgoTypeDateTime of 'a
| ErgoTypeDuration of 'a
| ErgoTypePeriod of 'a
| ErgoTypeClassRef of 'a * 'n
| ErgoTypeOption of 'a * ('a, 'n) ergo_type
| ErgoTypeRecord of 'a * (char list * ('a, 'n) ergo_type) list
| ErgoTypeArray of 'a * ('a, 'n) ergo_type
| ErgoTypeSum of 'a * ('a, 'n) ergo_type * ('a, 'n) ergo_type

type ('a, 'n) ergo_type_signature = { type_signature_annot : 'a;
                                      type_signature_params : (char list * ('a,
                                                              'n) ergo_type)
                                                              list;
                                      type_signature_output : ('a, 'n)
                                                              ergo_type option;
                                      type_signature_emits : ('a, 'n)
                                                             ergo_type option }

type ('a, 'n) ergo_type_declaration_desc =
| ErgoTypeEnum of char list list
| ErgoTypeTransaction of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeConcept of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeEvent of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeAsset of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeParticipant of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeGlobal of ('a, 'n) ergo_type
| ErgoTypeFunction of ('a, 'n) ergo_type_signature
| ErgoTypeContract of ('a, 'n) ergo_type * ('a, 'n) ergo_type
   * (char list * ('a, 'n) ergo_type_signature) list

type ('a, 'n) ergo_type_declaration = { type_declaration_annot : 'a;
                                        type_declaration_name : local_name;
                                        type_declaration_type : ('a, 'n)
                                                                ergo_type_declaration_desc }

val type_declaration_is_abstract :
  ('a1, 'a2) ergo_type_declaration_desc -> is_abstract

val type_declaration_is_enum :
  ('a1, 'a2) ergo_type_declaration_desc -> char list list option

type lrergo_type = (provenance, relative_name) ergo_type

type lrergo_type_signature = (provenance, relative_name) ergo_type_signature

type lrergo_type_declaration_desc =
  (provenance, relative_name) ergo_type_declaration_desc

type lrergo_type_declaration =
  (provenance, relative_name) ergo_type_declaration

type laergo_type = (provenance, absolute_name) ergo_type

type laergo_type_signature = (provenance, absolute_name) ergo_type_signature

type laergo_type_declaration =
  (provenance, absolute_name) ergo_type_declaration

type laergo_type_declaration_desc =
  (provenance, absolute_name) ergo_type_declaration_desc

val lift_default_emits_type : provenance -> laergo_type option -> laergo_type

val lift_default_state_type : provenance -> laergo_type option -> laergo_type

val default_throws_type : provenance -> laergo_type

val mk_success_type :
  provenance -> laergo_type -> laergo_type -> laergo_type -> laergo_type

val mk_error_type : provenance -> laergo_type -> laergo_type

val mk_output_type : provenance -> laergo_type -> laergo_type -> laergo_type

val fix_nothing : absolute_name -> (absolute_name * absolute_name) list

val fix_transaction : absolute_name -> (absolute_name * char list) list

val fix_event : absolute_name -> (absolute_name * char list) list

val fix_asset : absolute_name -> (absolute_name * char list) list

val fix_participant : absolute_name -> (absolute_name * char list) list

val extends_rel :
  (absolute_name -> (absolute_name * absolute_name) list) -> absolute_name ->
  absolute_name extends -> (absolute_name * absolute_name) list

val type_declaration_desc_extend_rel :
  absolute_name -> laergo_type_declaration_desc ->
  (absolute_name * absolute_name) list

val type_declaration_extend_rel :
  laergo_type_declaration -> (absolute_name * absolute_name) list

val type_name_of_type : laergo_type -> char list option

val label_of_decl : laergo_type_declaration -> char list

val name_of_decl : laergo_type_declaration -> char list

val decls_table :
  laergo_type_declaration list -> (char list * laergo_type_declaration) list

val edge_of_decl :
  (char list * laergo_type_declaration) list -> laergo_type_declaration ->
  laergo_type_declaration * laergo_type_declaration list

val graph_of_decls :
  laergo_type_declaration list ->
  (laergo_type_declaration * laergo_type_declaration list) list

val sort_decls : laergo_type_declaration list -> laergo_type_declaration list

val sort_given_topo_order :
  laergo_type_declaration list -> ('a1 -> char list) -> 'a1 list -> 'a1 list
