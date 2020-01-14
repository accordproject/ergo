open Provenance
open QLib

type ergo_nnrc_expr = QcertCodeGen.nnrc_expr

type ergo_nnrc_type = qcert_type

type ergo_nnrc_lambda = { lambdan_provenance : provenance;
                          lambdan_params : (char list * ergo_nnrc_type) list;
                          lambdan_output : ergo_nnrc_type;
                          lambdan_body : ergo_nnrc_expr }

type ergo_nnrc_function_table = { function_tablen_provenance : provenance;
                                  function_tablen_funs : (char list * ergo_nnrc_lambda)
                                                         list }

type ergo_nnrc_declaration =
| DNFunc of char list * ergo_nnrc_lambda
| DNFuncTable of char list * ergo_nnrc_function_table

type ergo_nnrc_module = { modulen_provenance : provenance;
                          modulen_namespace : char list;
                          modulen_declarations : ergo_nnrc_declaration list }
