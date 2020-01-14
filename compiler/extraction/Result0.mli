open Ast
open BinaryOperators
open CoqLibAdd
open Data
open DataResult
open Datatypes
open Lift
open List0
open ListAdd
open Misc
open Names
open NativeString
open Provenance
open QcertData
open Result
open String0
open UnaryOperators

type eerror =
| ESystemError of provenance * char list
| EParseError of provenance * char list
| ECompilationError of provenance * char list
| ETypeError of provenance * char list
| ERuntimeError of provenance * char list

type ewarning =
| EWarning of provenance * char list

type 'a eresult = ('a * ewarning list, eerror) coq_Result

val esuccess : 'a1 -> ewarning list -> 'a1 eresult

val efailure : eerror -> 'a1 eresult

val eolift : ('a1 -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult

val eolift_warning :
  (('a1 * ewarning list) -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult

val elift : ('a1 -> 'a2) -> 'a1 eresult -> 'a2 eresult

val elift2 : ('a1 -> 'a2 -> 'a3) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult

val elift3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult ->
  'a4 eresult

val elift_fold_left :
  ('a1 -> 'a2 -> 'a1 eresult) -> 'a2 list -> 'a1 -> 'a1 eresult

val emaplift : ('a1 -> 'a2 eresult) -> 'a1 list -> 'a2 list eresult

val elift_context_fold_left :
  ('a3 -> 'a1 -> ('a2 * 'a3) eresult) -> 'a1 list -> 'a3 -> ('a2 list * 'a3)
  eresult

val eflatmaplift : ('a1 -> 'a2 list eresult) -> 'a1 list -> 'a2 list eresult

val eresult_of_option : 'a1 option -> eerror -> ewarning list -> 'a1 eresult

val eolift2 :
  ('a1 -> 'a2 -> 'a3 eresult) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult

val elift_maybe : ('a1 -> 'a1 eresult option) -> 'a1 eresult -> 'a1 eresult

val elift_fail : (eerror -> 'a1 eresult) -> 'a1 eresult -> 'a1 eresult

val elift_both : ('a1 -> 'a2) -> (eerror -> 'a2) -> 'a1 eresult -> 'a2

val elift2_both :
  ('a1 -> 'a2 -> 'a3) -> (eerror -> 'a3) -> 'a1 eresult -> 'a2 eresult -> 'a3

val eerror_of_qerror : provenance -> qerror -> eerror

val eresult_of_qresult : provenance -> 'a1 qresult -> 'a1 eresult

val format_error : char list -> provenance -> char list -> char list

val clause_call_not_on_contract_error : provenance -> 'a1 eresult

val use_contract_not_in_contract_error : provenance -> 'a1 eresult

val call_clause_not_in_contract_error : provenance -> char list -> 'a1 eresult

val not_in_clause_error : provenance -> 'a1 eresult

val case_option_not_on_either_error : provenance -> 'a1 eresult

val set_state_on_non_brand_error : provenance -> char list -> 'a1 eresult

val import_not_found_error : provenance -> char list -> 'a1 eresult

val type_name_not_found_error : provenance -> char list -> 'a1 eresult

val namespace_not_found_error : provenance -> char list -> 'a1 eresult

val variable_name_not_found_error : provenance -> char list -> 'a1 eresult

val enum_name_not_found_error : provenance -> char list -> 'a1 eresult

val function_name_not_found_error : provenance -> char list -> 'a1 eresult

val contract_name_not_found_error : provenance -> char list -> 'a1 eresult

val import_name_not_found_error :
  provenance -> char list -> char list -> 'a1 eresult

val main_parameter_mismatch_error : provenance -> 'a1 eresult

val main_at_least_one_parameter_error : provenance -> 'a1 eresult

val function_not_found_error : provenance -> char list -> 'a1 eresult

val call_params_error : provenance -> char list -> 'a1 eresult

val eval_unary_operator_error :
  provenance -> ergo_unary_operator -> 'a1 eresult

val eval_binary_operator_error :
  provenance -> ergo_binary_operator -> 'a1 eresult

val eval_unary_builtin_error :
  provenance -> QLib.QcertOps.Unary.op -> 'a1 eresult

val eval_binary_builtin_error :
  provenance -> QLib.QcertOps.Binary.op -> 'a1 eresult

val eval_if_not_boolean_error : provenance -> 'a1 eresult

val eval_foreach_not_on_array_error : provenance -> 'a1 eresult

val template_type_not_found_error : provenance -> 'a1 eresult

val more_than_one_template_type_error : provenance -> char list -> 'a1 eresult

val no_ergo_module_error : provenance -> 'a1 eresult

val built_in_function_not_found_error : provenance -> char list -> 'a1 eresult

val built_in_function_without_body_error :
  provenance -> char list -> 'a1 eresult

val enforce_error_content : provenance -> char list -> QLib.QcertData.data

val default_match_error_content : provenance -> data

val should_have_one_contract_error : provenance -> 'a1 eresult

val this_in_calculus_error : provenance -> 'a1 eresult

val contract_in_calculus_error : provenance -> 'a1 eresult

val clause_in_calculus_error : provenance -> 'a1 eresult

val operator_in_calculus_error : provenance -> 'a1 eresult

val state_in_calculus_error : provenance -> 'a1 eresult

val text_in_calculus_error : provenance -> 'a1 eresult

val complex_foreach_in_calculus_error : provenance -> 'a1 eresult

val print_in_calculus_error : provenance -> 'a1 eresult

val function_not_inlined_error :
  provenance -> char list -> char list -> 'a1 eresult

val function_in_group_not_inlined_error :
  provenance -> char list -> char list -> 'a1 eresult

val as_in_calculus_error : provenance -> 'a1 eresult

val no_duplicates_with_err :
  char list list -> 'a1 -> (char list option -> eerror) -> 'a1 eresult

val duplicate_function_params_error :
  provenance -> char list -> char list option -> eerror

val duplicate_function_params_check :
  provenance -> char list -> char list list -> 'a1 -> 'a1 eresult

val duplicate_clause_for_request_error :
  provenance -> char list option -> eerror

val duplicate_clause_for_request_check :
  provenance -> char list list -> 'a1 -> 'a1 eresult

val warning_no_else : provenance -> ewarning

val warning_global_shadowing : provenance -> char list -> ewarning

type result_file = { res_contract_name : char list option;
                     res_file : char list; res_content : nstring }
