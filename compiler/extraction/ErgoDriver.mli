open Assoc
open Datatypes
open Ergo
open ErgoAssembly
open ErgoC
open ErgoCEval
open ErgoCEvalContext
open ErgoCExpand
open ErgoCInline
open ErgoCT
open ErgoCTtoErgoNNRC
open ErgoCTypecheck
open ErgoCTypecheckContext
open ErgoCompContext
open ErgoImptoES6
open ErgoImptoWasmAst
open ErgoNNRC
open ErgoNNRCtoErgoImp
open ErgoNNRCtoJava
open ErgoNameResolve
open ErgoType
open ErgoTypetoQcertType
open ErgoWasmBinary
open ErgotoErgoC
open List0
open Misc
open Names
open NamespaceContext
open PrintTypedData
open Provenance
open QLib
open Result0
open String0
open TBrandModel
open WasmAsttoWasmBinary

val resolve_inputs_opt :
  lrergo_input list -> (char list * lrergo_expr) list option ->
  ((laergo_module list * laergo_module option) * namespace_ctxt) eresult

val resolve_inputs :
  lrergo_input list -> (char list * lrergo_expr) list option ->
  ((laergo_module list * laergo_module) * namespace_ctxt) eresult

val resolve_inputs_no_main :
  lrergo_input list -> (char list * lrergo_expr) list option ->
  (laergo_module list * namespace_ctxt) eresult

val just_resolved_inputs :
  lrergo_input list -> (char list * lrergo_expr) list option -> laergo_module
  list eresult

val brand_model_from_inputs :
  lrergo_input list -> (QcertType.tbrand_model * laergo_type_declaration
  list) eresult

val init_compilation_context_from_inputs :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
  -> laergo_type_declaration list -> ((laergo_module
  list * laergo_module) * compilation_context) eresult

val init_compilation_context_from_inputs_no_main :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
  -> laergo_type_declaration list -> (laergo_module
  list * compilation_context) eresult

val ergo_module_to_ergoct :
  brand_model -> compilation_context -> laergo_module ->
  (ergoct_module * compilation_context) eresult

val ergo_modules_to_ergoct :
  brand_model -> compilation_context -> laergo_module list -> (ergoct_module
  list * compilation_context) eresult

val ergo_declaration_to_ergoc :
  brand_model -> compilation_context -> lrergo_declaration ->
  (ergoc_declaration list * compilation_context) eresult

val ergo_declaration_to_ergoct_inlined :
  brand_model -> compilation_context -> lrergo_declaration ->
  (ergoct_declaration list * compilation_context) eresult

val compilation_context_from_inputs :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
  -> laergo_type_declaration list -> (laergo_module * compilation_context)
  eresult

val compilation_context_from_inputs_no_main :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
  -> laergo_type_declaration list -> compilation_context eresult

val ergo_module_to_java :
  brand_model -> compilation_context -> laergo_module ->
  (ergo_nnrc_module * QcertCodeGen.java) eresult

val ergo_module_to_java_top :
  lrergo_input list -> (char list * lrergo_expr) list option -> result_file
  eresult

val ergoc_module_to_es6 :
  brand_model -> char list -> (provenance, absolute_name) ergo_type option ->
  (char list * (provenance, absolute_name) ergo_type_signature) list ->
  ergo_nnrc_module -> QcertCodeGen.ejavascript

val ergoc_module_to_wasm :
  brand_model -> char list -> ergo_nnrc_module -> wasm

val ergo_module_to_es6_top :
  lrergo_input list -> (char list * lrergo_expr) list option -> result_file
  eresult

val ergo_module_to_wasm_top :
  lrergo_input list -> (char list * lrergo_expr) list option -> result_file
  eresult

type repl_context = { repl_context_eval_ctxt : eval_context;
                      repl_context_comp_ctxt : compilation_context }

val init_repl_context :
  brand_model -> lrergo_input list -> repl_context eresult

val update_repl_ctxt_comp_ctxt :
  brand_model -> repl_context -> compilation_context -> repl_context

val update_repl_ctxt_type_ctxt :
  brand_model -> repl_context -> type_context -> repl_context

val update_repl_ctxt_eval_ctxt :
  brand_model -> repl_context -> eval_context -> repl_context

val lift_repl_ctxt :
  brand_model -> repl_context -> ((qcert_type option * qcert_data
  option) * repl_context) eresult -> repl_context

val ergoc_repl_eval_declaration :
  brand_model -> repl_context -> ergoct_declaration -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergoct_repl_eval_declarations :
  brand_model -> repl_context -> ergoct_declaration list -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergoct_eval_decl_via_calculus :
  brand_model -> repl_context -> lrergo_declaration -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergo_string_of_result :
  brand_model -> repl_context -> ((qcert_type option * qcert_data
  option) * repl_context) eresult -> char list eresult

val ergoct_repl_eval_decl :
  brand_model -> repl_context -> lrergo_declaration -> char list
  eresult * repl_context

val refresh_brand_model_in_comp_ctxt :
  brand_model -> compilation_context ->
  (QcertType.tbrand_model * compilation_context) eresult

val refresh_brand_model :
  brand_model -> repl_context -> (QcertType.tbrand_model * repl_context)
  eresult
