open Assoc
open Data
open Datatypes
open List0
open Names
open Provenance
open Result0
open String0

type enum_flag =
| EnumNone
| EnumValue of data
| EnumType of (char list * data) list

type name_table = (local_name * (absolute_name * enum_flag)) list

type namespace_table = { namespace_table_types : name_table;
                         namespace_table_constants : name_table;
                         namespace_table_functions : name_table;
                         namespace_table_contracts : name_table }

val empty_namespace_table : namespace_table

val import_one_type_to_namespace_table :
  local_name -> absolute_name -> namespace_table

val import_one_enum_type_to_namespace_table :
  local_name -> absolute_name -> (char list * data) list -> namespace_table

val import_one_constant_to_namespace_table :
  local_name -> absolute_name -> namespace_table

val namespace_table_app :
  namespace_table -> namespace_table -> namespace_table

val lookup_type_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_constant_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_econstant_name :
  provenance -> namespace_table -> local_name -> (absolute_name * data)
  eresult

val lookup_function_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_contract_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val add_type_to_namespace_table :
  local_name -> absolute_name -> enum_flag -> namespace_table ->
  namespace_table

val add_constant_to_namespace_table :
  local_name -> absolute_name -> enum_flag -> namespace_table ->
  namespace_table

val add_constants_to_namespace_table :
  (local_name * (absolute_name * enum_flag)) list -> namespace_table ->
  namespace_table

val hide_constant_from_namespace_table :
  local_name -> namespace_table -> namespace_table

val add_function_to_namespace_table :
  local_name -> absolute_name -> namespace_table -> namespace_table

val add_contract_to_namespace_table :
  local_name -> absolute_name -> namespace_table -> namespace_table

type abstract_ctxt = char list list

type namespace_ctxt = { namespace_ctxt_modules : (namespace_name * namespace_table)
                                                 list;
                        namespace_ctxt_namespace : namespace_name;
                        namespace_ctxt_current_module : namespace_table;
                        namespace_ctxt_current_in_scope : namespace_table;
                        namespace_ctxt_abstract : abstract_ctxt }

val empty_namespace_ctxt : namespace_name -> namespace_ctxt

val update_namespace_context_modules :
  namespace_ctxt -> namespace_name -> (namespace_table -> namespace_table) ->
  namespace_ctxt

val update_namespace_context_current_both :
  namespace_ctxt -> (namespace_table -> namespace_table) -> namespace_ctxt

val update_namespace_context_abstract :
  namespace_ctxt -> abstract_ctxt -> namespace_ctxt

val add_type_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  enum_flag -> namespace_ctxt

val add_constant_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> enum_flag ->
  absolute_name -> namespace_ctxt

val add_function_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  namespace_ctxt

val add_contract_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  namespace_ctxt

val add_type_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> enum_flag -> namespace_ctxt

val add_constant_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> enum_flag -> namespace_ctxt

val add_econstants_to_namespace_ctxt_current :
  namespace_ctxt -> namespace_name ->
  (local_name * (absolute_name * enum_flag)) list -> namespace_ctxt

val hide_constant_from_namespace_ctxt_current :
  namespace_ctxt -> local_name -> namespace_ctxt

val hide_constants_from_namespace_ctxt_current :
  namespace_ctxt -> local_name list -> namespace_ctxt

val add_function_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt

val add_contract_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt

val new_namespace_scope : namespace_ctxt -> namespace_name -> namespace_ctxt

val local_namespace_scope : namespace_ctxt -> namespace_name -> namespace_ctxt

val verify_name :
  (provenance -> namespace_table -> local_name -> 'a1 eresult) -> provenance
  -> namespace_ctxt -> namespace_name -> local_name -> 'a1 eresult

val verify_type_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_constant_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_econstant_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  (absolute_name * data) eresult

val verify_function_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_contract_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val resolve_type_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_constant_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_econstant_name :
  provenance -> namespace_ctxt -> relative_name -> (absolute_name * data)
  eresult

val resolve_all_constant_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_function_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_contract_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult
