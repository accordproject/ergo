open BrandRelation
open Names
open QLib

type type_context = { type_context_global_env : (char list * qcert_type) list;
                      type_context_local_env : (char list * qcert_type) list }

(** val type_context_update_global_env :
    brand_relation -> type_context -> char list -> qcert_type -> type_context **)

let type_context_update_global_env _ ctxt name value =
  { type_context_global_env = ((name,
    value) :: ctxt.type_context_global_env); type_context_local_env =
    ctxt.type_context_local_env }

(** val type_context_update_local_env :
    brand_relation -> type_context -> char list -> qcert_type -> type_context **)

let type_context_update_local_env _ ctxt name value =
  { type_context_global_env = ctxt.type_context_global_env;
    type_context_local_env = ((name, value) :: ctxt.type_context_local_env) }

(** val type_context_set_local_env :
    brand_relation -> type_context -> (char list * qcert_type) list ->
    type_context **)

let type_context_set_local_env _ ctxt new_local_env =
  { type_context_global_env = ctxt.type_context_global_env;
    type_context_local_env = new_local_env }

(** val empty_type_context : brand_relation -> type_context **)

let empty_type_context br =
  { type_context_global_env = ((options,
    (QcertType.tbrand br (default_options :: []))) :: ((current_time,
    (QcertType.tdateTime br)) :: ((this_contract,
    (QcertType.tunit br)) :: ((this_state,
    (QcertType.tunit br)) :: ((this_emit,
    (QcertType.tcoll br (QcertType.tbottom br))) :: [])))));
    type_context_local_env = [] }
