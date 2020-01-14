open String0

type local_name = char list

type namespace_name = char list

type enum_name = char list

type namespace_prefix = namespace_name option

type relative_name = namespace_prefix * local_name

type absolute_name = char list

val absolute_name_of_local_name :
  namespace_name -> local_name -> absolute_name

val enum_namespace : namespace_name -> enum_name -> namespace_name

val clause_main_name : local_name

val clause_init_name : local_name

val this_this : char list

val this_contract : char list

val this_state : char list

val this_emit : char list

val this_response : char list

val local_state : char list

val local_emit : char list

val current_time : char list

val options : char list

val accordproject_concerto_namespace : char list

val accordproject_runtime_namespace : char list

val accordproject_contract_namespace : char list

val accordproject_stdlib_namespace : char list

val accordproject_time_namespace : char list

val accordproject_top_namespace : char list

val accordproject_options_namespace : char list

val accordproject_template_namespace : char list

val default_enum_absolute_name : char list

val default_event_absolute_name : char list

val default_transaction_absolute_name : char list

val default_asset_absolute_name : char list

val default_participant_absolute_name : char list

val default_contract_absolute_name : char list

val default_clause_absolute_name : char list

val default_request_absolute_name : char list

val default_state_absolute_name : char list

val default_error_absolute_name : char list

val default_options : char list

val function_name_in_table : char list option -> char list -> char list

val no_namespace : char list
