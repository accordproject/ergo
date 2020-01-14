open Data
open Names
open QcertData

type eval_context = { eval_context_global_env : (char list * QLib.qcert_data)
                                                list;
                      eval_context_local_env : (char list * QLib.qcert_data)
                                               list }

(** val eval_context_update_global_env :
    eval_context -> char list -> QLib.qcert_data -> eval_context **)

let eval_context_update_global_env ctxt name value =
  { eval_context_global_env = ((name,
    value) :: ctxt.eval_context_global_env); eval_context_local_env =
    ctxt.eval_context_local_env }

(** val eval_context_update_local_env :
    eval_context -> char list -> QLib.qcert_data -> eval_context **)

let eval_context_update_local_env ctxt name value =
  { eval_context_global_env = ctxt.eval_context_global_env;
    eval_context_local_env = ((name, value) :: ctxt.eval_context_local_env) }

(** val empty_eval_context : eval_context **)

let empty_eval_context =
  { eval_context_global_env = ((options, (Coq_dbrand
    ((default_options :: []), (Coq_drec
    ((('w'::('r'::('a'::('p'::('V'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::[]))))))))))))),
    (Coq_dbool
    false)) :: ((('t'::('e'::('m'::('p'::('l'::('a'::('t'::('e'::[])))))))),
    (Coq_dbool false)) :: [])))))) :: ((current_time, (Coq_dforeign
    (Obj.magic (Coq_enhanceddateTime enhanceddateTime_now)))) :: ((this_contract,
    Coq_dunit) :: ((this_state, Coq_dunit) :: ((this_emit, (Coq_dcoll
    [])) :: []))))); eval_context_local_env = [] }
