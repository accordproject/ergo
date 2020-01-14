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

(** val type_declaration_is_abstract :
    ('a1, 'a2) ergo_type_declaration_desc -> is_abstract **)

let type_declaration_is_abstract = function
| ErgoTypeTransaction (isabs, _, _) -> isabs
| ErgoTypeConcept (isabs, _, _) -> isabs
| ErgoTypeEvent (isabs, _, _) -> isabs
| ErgoTypeAsset (isabs, _, _) -> isabs
| ErgoTypeParticipant (isabs, _, _) -> isabs
| _ -> false

(** val type_declaration_is_enum :
    ('a1, 'a2) ergo_type_declaration_desc -> char list list option **)

let type_declaration_is_enum = function
| ErgoTypeEnum enum_list -> Some enum_list
| _ -> None

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

(** val lift_default_emits_type :
    provenance -> laergo_type option -> laergo_type **)

let lift_default_emits_type prov = function
| Some e -> e
| None -> ErgoTypeClassRef (prov, default_event_absolute_name)

(** val lift_default_state_type :
    provenance -> laergo_type option -> laergo_type **)

let lift_default_state_type prov = function
| Some e -> e
| None -> ErgoTypeClassRef (prov, default_state_absolute_name)

(** val default_throws_type : provenance -> laergo_type **)

let default_throws_type prov =
  ErgoTypeClassRef (prov, default_error_absolute_name)

(** val mk_success_type :
    provenance -> laergo_type -> laergo_type -> laergo_type -> laergo_type **)

let mk_success_type prov response_type state_type emit_type =
  ErgoTypeRecord (prov, ((this_response, response_type) :: ((this_state,
    state_type) :: ((this_emit, (ErgoTypeArray (prov, emit_type))) :: []))))

(** val mk_error_type : provenance -> laergo_type -> laergo_type **)

let mk_error_type _ throw_type =
  throw_type

(** val mk_output_type :
    provenance -> laergo_type -> laergo_type -> laergo_type **)

let mk_output_type prov success_type error_type =
  ErgoTypeSum (prov, success_type, error_type)

(** val fix_nothing :
    absolute_name -> (absolute_name * absolute_name) list **)

let fix_nothing _ =
  []

(** val fix_transaction :
    absolute_name -> (absolute_name * char list) list **)

let fix_transaction to0 =
  if string_dec to0 default_transaction_absolute_name
  then []
  else (to0, default_transaction_absolute_name) :: []

(** val fix_event : absolute_name -> (absolute_name * char list) list **)

let fix_event to0 =
  if string_dec to0 default_event_absolute_name
  then []
  else (to0, default_event_absolute_name) :: []

(** val fix_asset : absolute_name -> (absolute_name * char list) list **)

let fix_asset to0 =
  if string_dec to0 default_asset_absolute_name
  then []
  else (to0, default_asset_absolute_name) :: []

(** val fix_participant :
    absolute_name -> (absolute_name * char list) list **)

let fix_participant to0 =
  if string_dec to0 default_participant_absolute_name
  then []
  else (to0, default_participant_absolute_name) :: []

(** val extends_rel :
    (absolute_name -> (absolute_name * absolute_name) list) -> absolute_name
    -> absolute_name extends -> (absolute_name * absolute_name) list **)

let extends_rel fix_none to0 = function
| Some from -> (to0, from) :: []
| None -> fix_none to0

(** val type_declaration_desc_extend_rel :
    absolute_name -> laergo_type_declaration_desc ->
    (absolute_name * absolute_name) list **)

let type_declaration_desc_extend_rel to0 = function
| ErgoTypeEnum _ -> extends_rel fix_nothing to0 None
| ErgoTypeTransaction (_, e, _) -> extends_rel fix_transaction to0 e
| ErgoTypeConcept (_, e, _) -> extends_rel fix_nothing to0 e
| ErgoTypeEvent (_, e, _) -> extends_rel fix_event to0 e
| ErgoTypeAsset (_, e, _) -> extends_rel fix_asset to0 e
| ErgoTypeParticipant (_, e, _) -> extends_rel fix_participant to0 e
| ErgoTypeContract (_, _, _) -> extends_rel fix_nothing to0 None
| _ -> []

(** val type_declaration_extend_rel :
    laergo_type_declaration -> (absolute_name * absolute_name) list **)

let type_declaration_extend_rel decl =
  type_declaration_desc_extend_rel decl.type_declaration_name
    decl.type_declaration_type

(** val type_name_of_type : laergo_type -> char list option **)

let type_name_of_type = function
| ErgoTypeClassRef (_, tname) -> Some tname
| _ -> None

(** val label_of_decl : laergo_type_declaration -> char list **)

let label_of_decl decl =
  decl.type_declaration_name

(** val name_of_decl : laergo_type_declaration -> char list **)

let name_of_decl =
  label_of_decl

(** val decls_table :
    laergo_type_declaration list -> (char list * laergo_type_declaration) list **)

let decls_table decls =
  map (fun d -> (d.type_declaration_name, d)) decls

(** val edge_of_decl :
    (char list * laergo_type_declaration) list -> laergo_type_declaration ->
    laergo_type_declaration * laergo_type_declaration list **)

let edge_of_decl dt decl =
  let outedges = type_declaration_extend_rel decl in
  (decl,
  (List0.concat
    (map (fun xy ->
      match lookup string_dec dt (snd xy) with
      | Some x -> x :: []
      | None -> []) outedges)))

(** val graph_of_decls :
    laergo_type_declaration list ->
    (laergo_type_declaration * laergo_type_declaration list) list **)

let graph_of_decls decls =
  let dt = decls_table decls in map (edge_of_decl dt) decls

(** val sort_decls :
    laergo_type_declaration list -> laergo_type_declaration list **)

let sort_decls decls =
  let decls0 = coq_coq_distinct name_of_decl decls in
  coq_coq_toposort label_of_decl name_of_decl (graph_of_decls decls0)

(** val sort_given_topo_order :
    laergo_type_declaration list -> ('a1 -> char list) -> 'a1 list -> 'a1 list **)

let sort_given_topo_order order label l =
  coq_coq_sort_given_topo_order order label_of_decl label name_of_decl l
