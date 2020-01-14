open BrandRelation
open Names
open QLib

type type_context = { type_context_global_env : (char list * qcert_type) list;
                      type_context_local_env : (char list * qcert_type) list }

val type_context_update_global_env :
  brand_relation -> type_context -> char list -> qcert_type -> type_context

val type_context_update_local_env :
  brand_relation -> type_context -> char list -> qcert_type -> type_context

val type_context_set_local_env :
  brand_relation -> type_context -> (char list * qcert_type) list ->
  type_context

val empty_type_context : brand_relation -> type_context
