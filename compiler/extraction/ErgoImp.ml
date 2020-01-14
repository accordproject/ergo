open Provenance
open QLib

type ergo_imp_lambda = QcertCodeGen.imp_ejson_function

type ergo_imp_function_table = QcertCodeGen.imp_ejson_lib

type ergo_imp_declaration =
| DIFunc of char list * ergo_imp_lambda
| DIFuncTable of char list * ergo_imp_function_table

type ergo_imp_module = { modulei_provenance : provenance;
                         modulei_namespace : char list;
                         modulei_declarations : ergo_imp_declaration list }
