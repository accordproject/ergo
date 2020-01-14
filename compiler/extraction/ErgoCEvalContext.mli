open Data
open Names
open QcertData

type eval_context = { eval_context_global_env : (char list * QLib.qcert_data)
                                                list;
                      eval_context_local_env : (char list * QLib.qcert_data)
                                               list }

val eval_context_update_global_env :
  eval_context -> char list -> QLib.qcert_data -> eval_context

val eval_context_update_local_env :
  eval_context -> char list -> QLib.qcert_data -> eval_context

val empty_eval_context : eval_context
