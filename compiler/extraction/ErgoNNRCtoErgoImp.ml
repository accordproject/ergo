open Datatypes
open ErgoImp
open ErgoNNRC
open List0
open QLib
open TBrandModel

(** val ergo_nnrc_function_to_imp :
    brand_model -> char list list -> ergo_nnrc_lambda -> ergo_imp_lambda **)

let ergo_nnrc_function_to_imp bm globals fbody =
  QcertCodeGen.nnrc_expr_to_imp_ejson_function bm globals fbody.lambdan_body

(** val ergo_nnrc_function_table_to_imp :
    brand_model -> char list list -> ergo_nnrc_function_table ->
    ergo_imp_function_table **)

let ergo_nnrc_function_table_to_imp bm globals ft =
  map (fun xy -> ((fst xy), (ergo_nnrc_function_to_imp bm globals (snd xy))))
    ft.function_tablen_funs

(** val ergo_nnrc_declaration_to_imp :
    brand_model -> char list list -> ergo_nnrc_declaration ->
    ergo_imp_declaration **)

let ergo_nnrc_declaration_to_imp bm globals = function
| DNFunc (fname, fbody) ->
  DIFunc (fname, (ergo_nnrc_function_to_imp bm globals fbody))
| DNFuncTable (cname, ft) ->
  DIFuncTable (cname, (ergo_nnrc_function_table_to_imp bm globals ft))

(** val ergo_nnrc_declarations_to_imp :
    brand_model -> ergo_nnrc_declaration list -> ergo_imp_declaration list **)

let ergo_nnrc_declarations_to_imp bm sl =
  map (ergo_nnrc_declaration_to_imp bm []) sl

(** val ergo_nnrc_module_to_imp :
    brand_model -> ergo_nnrc_module -> ergo_imp_module **)

let ergo_nnrc_module_to_imp bm m =
  { modulei_provenance = m.modulen_provenance; modulei_namespace =
    m.modulen_namespace; modulei_declarations =
    (ergo_nnrc_declarations_to_imp bm m.modulen_declarations) }
