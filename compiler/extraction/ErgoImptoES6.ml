open BrandRelation
open CompDriver
open Datatypes
open EmitUtil
open ErgoImp
open ErgoType
open JavaScriptAst
open List0
open Names
open NativeString
open Provenance
open QLib
open String0
open TBrandModel
open Version

(** val accord_annotation :
    bool -> char list -> char list -> char list -> char list -> char list ->
    nstring -> nstring -> nstring **)

let accord_annotation generated _ request_type response_type emit_type state_type eol _ =
  if generated
  then nstring_quote []
  else nstring_append eol
         (nstring_append (nstring_quote ('/'::('*'::('*'::[]))))
           (nstring_append eol
             (nstring_append
               (nstring_quote
                 (' '::('*'::(' '::('E'::('x'::('e'::('c'::('u'::('t'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('m'::('a'::('r'::('t'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::[]))))))))))))))))))))))))))))
               (nstring_append eol
                 (nstring_append
                   (nstring_quote
                     (' '::('*'::(' '::('@'::('p'::('a'::('r'::('a'::('m'::(' '::('{'::('C'::('o'::('n'::('t'::('e'::('x'::('t'::('}'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::(' '::('-'::(' '::('t'::('h'::('e'::(' '::('A'::('c'::('c'::('o'::('r'::('d'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))
                   (nstring_append eol
                     (nstring_append
                       (nstring_quote
                         (' '::('*'::(' '::('@'::('p'::('a'::('r'::('a'::('m'::(' '::('{'::[]))))))))))))
                       (nstring_append (nstring_quote request_type)
                         (nstring_append
                           (nstring_quote
                             ('}'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::('.'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::(' '::('-'::(' '::('t'::('h'::('e'::(' '::('i'::('n'::('c'::('o'::('m'::('i'::('n'::('g'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))))))))))))))))))))))))))))))))
                           (nstring_append eol
                             (nstring_append
                               (nstring_quote
                                 (' '::('*'::(' '::('@'::('p'::('a'::('r'::('a'::('m'::(' '::('{'::[]))))))))))))
                               (nstring_append (nstring_quote response_type)
                                 (nstring_append
                                   (nstring_quote
                                     ('}'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::('.'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::(' '::('-'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[]))))))))))))))))))))))))))))))))))
                                   (nstring_append eol
                                     (nstring_append
                                       (nstring_quote
                                         (' '::('*'::(' '::('@'::('p'::('a'::('r'::('a'::('m'::(' '::('{'::[]))))))))))))
                                       (nstring_append
                                         (nstring_quote emit_type)
                                         (nstring_append
                                           (nstring_quote
                                             ('}'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::('.'::('e'::('m'::('i'::('t'::(' '::('-'::(' '::('t'::('h'::('e'::(' '::('e'::('m'::('i'::('t'::('t'::('e'::('d'::(' '::('e'::('v'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))))))))))))
                                           (nstring_append eol
                                             (nstring_append
                                               (nstring_quote
                                                 (' '::('*'::(' '::('@'::('p'::('a'::('r'::('a'::('m'::(' '::('{'::[]))))))))))))
                                               (nstring_append
                                                 (nstring_quote state_type)
                                                 (nstring_append
                                                   (nstring_quote
                                                     ('}'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::('.'::('s'::('t'::('a'::('t'::('e'::(' '::('-'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('t'::('e'::[]))))))))))))))))))))))))))))
                                                   (nstring_append eol
                                                     (nstring_append
                                                       (nstring_quote
                                                         (' '::('*'::('/'::[]))))
                                                       eol)))))))))))))))))))))))

(** val ergo_imp_function_to_javascript_ast :
    brand_model -> char list -> ergo_imp_lambda -> char list option -> js_ast **)

let ergo_imp_function_to_javascript_ast bm fname fbody tname =
  let fnameSafe =
    QcertCodeGen.javascript_identifier_sanitizer
      (function_name_in_table tname fname)
  in
  QcertCodeGen.imp_function_to_javascript_ast bm fnameSafe fbody

(** val ergo_imp_function_table_to_javascript_ast :
    brand_model -> char list -> ergo_imp_function_table -> js_ast **)

let ergo_imp_function_table_to_javascript_ast bm cname ft =
  let cnameSafe = QcertCodeGen.javascript_identifier_sanitizer cname in
  QcertCodeGen.imp_function_table_to_javascript_ast bm cnameSafe ft

(** val preamble : js_ast **)

let preamble =
  (Coq_comment
    (append
      (' '::('G'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::('d'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('e'::('r'::('g'::('o'::(' '::('v'::('e'::('r'::('s'::('i'::('o'::('n'::(' '::[]))))))))))))))))))))))))))))))
      (append ergo_version (' '::[])))) :: (Coq_strictmode :: ((Coq_comment
    ('e'::('s'::('l'::('i'::('n'::('t'::('-'::('d'::('i'::('s'::('a'::('b'::('l'::('e'::(' '::('n'::('o'::('-'::('u'::('n'::('u'::('s'::('e'::('d'::('-'::('v'::('a'::('r'::('s'::[])))))))))))))))))))))))))))))) :: ((Coq_comment
    ('e'::('s'::('l'::('i'::('n'::('t'::('-'::('d'::('i'::('s'::('a'::('b'::('l'::('e'::(' '::('n'::('o'::('-'::('u'::('n'::('d'::('e'::('f'::[])))))))))))))))))))))))) :: ((Coq_comment
    ('e'::('s'::('l'::('i'::('n'::('t'::('-'::('d'::('i'::('s'::('a'::('b'::('l'::('e'::(' '::('n'::('o'::('-'::('v'::('a'::('r'::[])))))))))))))))))))))) :: []))))

(** val postamble : js_ast **)

let postamble =
  (Coq_comment
    ('e'::('s'::('l'::('i'::('n'::('t'::('-'::('e'::('n'::('a'::('b'::('l'::('e'::(' '::('n'::('o'::('-'::('u'::('n'::('u'::('s'::('e'::('d'::('-'::('v'::('a'::('r'::('s'::[]))))))))))))))))))))))))))))) :: ((Coq_comment
    ('e'::('s'::('l'::('i'::('n'::('t'::('-'::('e'::('n'::('a'::('b'::('l'::('e'::(' '::('n'::('o'::('-'::('u'::('n'::('d'::('e'::('f'::[]))))))))))))))))))))))) :: [])

(** val ergo_imp_declaration_to_javascript_ast :
    brand_model -> ergo_imp_declaration -> js_ast **)

let ergo_imp_declaration_to_javascript_ast bm = function
| DIFunc (fname, fbody) ->
  ergo_imp_function_to_javascript_ast bm fname fbody None
| DIFuncTable (cname, ft) ->
  ergo_imp_function_table_to_javascript_ast bm cname ft

(** val ergo_imp_declarations_to_javascript_ast :
    brand_model -> ergo_imp_declaration list -> js_ast **)

let ergo_imp_declarations_to_javascript_ast bm sl =
  List0.concat (map (ergo_imp_declaration_to_javascript_ast bm) sl)

(** val ergo_imp_module_to_javascript_ast :
    brand_model -> ergo_imp_module -> topdecl list **)

let ergo_imp_module_to_javascript_ast bm p =
  app preamble
    (app
      ((QcertCodeGen.javascript_of_inheritance
         (brand_relation_brands bm.brand_model_relation)) :: [])
      (app
        (ergo_imp_declarations_to_javascript_ast bm p.modulei_declarations)
        postamble))

(** val ergo_imp_module_to_javascript_top :
    brand_model -> (char list * char list) list -> ergo_imp_module ->
    QcertCodeGen.ejavascript **)

let ergo_imp_module_to_javascript_top bm _ p =
  js_ast_to_javascript (ergo_imp_module_to_javascript_ast bm p)

(** val wrapper_function_for_clause :
    bool -> char list -> char list -> char list -> char list -> char list ->
    char list -> char list -> char list -> nstring -> nstring -> nstring **)

let wrapper_function_for_clause generated fun_name request_param request_type response_type emit_type state_type contract_name clause_name eol quotel =
  nstring_append
    (accord_annotation generated clause_name request_type response_type
      emit_type state_type eol quotel)
    (nstring_append eol
      (nstring_append
        (nstring_quote
          ('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))
        (nstring_append (nstring_quote fun_name)
          (nstring_append
            (nstring_quote
              ('('::('c'::('o'::('n'::('t'::('e'::('x'::('t'::(')'::(' '::('{'::[]))))))))))))
            (nstring_append eol
              (nstring_append
                (nstring_quote
                  (' '::(' '::('l'::('e'::('t'::(' '::('p'::('c'::('o'::('n'::('t'::('e'::('x'::('t'::(' '::('='::(' '::('O'::('b'::('j'::('e'::('c'::('t'::('.'::('a'::('s'::('s'::('i'::('g'::('n'::('('::('c'::('o'::('n'::('t'::('e'::('x'::('t'::(','::(' '::('{'::(' '::('\''::[]))))))))))))))))))))))))))))))))))))))))))))
                (nstring_append (nstring_quote request_param)
                  (nstring_append
                    (nstring_quote
                      ('\''::(' '::(':'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::('.'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::(' '::('}'::(')'::(';'::[]))))))))))))))))))))))))
                    (nstring_append eol
                      (nstring_append
                        (nstring_quote
                          (' '::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::[]))))))))))
                        (nstring_append (nstring_quote contract_name)
                          (nstring_append (nstring_quote ('.'::[]))
                            (nstring_append (nstring_quote clause_name)
                              (nstring_append
                                (nstring_quote
                                  ('('::('p'::('c'::('o'::('n'::('t'::('e'::('x'::('t'::(')'::(';'::[]))))))))))))
                                (nstring_append eol (nstring_quote ('}'::[])))))))))))))))))

(** val apply_wrapper_function :
    char list -> char list ->
    ((((char list * char list) * char list) * char list) * char list) ->
    nstring -> nstring -> nstring **)

let apply_wrapper_function contract_name contract_state_type signature eol quotel =
  let (p, emit_type) = signature in
  let (p0, response_type) = p in
  let (p1, request_type) = p0 in
  let (clause_name, request_name) = p1 in
  let fun_name =
    QcertCodeGen.javascript_identifier_sanitizer
      (append contract_name (append ('_'::[]) clause_name))
  in
  let cname = QcertCodeGen.javascript_identifier_sanitizer contract_name in
  if string_dec clause_name clause_init_name
  then nstring_quote []
  else wrapper_function_for_clause false fun_name request_name request_type
         response_type emit_type contract_state_type cname clause_name eol
         quotel

(** val wrapper_functions :
    char list ->
    (((((char list * char list) * char list) * char list) * char list)
    list * char list) -> nstring -> nstring -> nstring **)

let wrapper_functions contract_name signatures eol quotel =
  nstring_concat eol
    (map (fun sig0 ->
      apply_wrapper_function contract_name (snd signatures) sig0 eol quotel)
      (fst signatures))

(** val javascript_of_module_with_dispatch :
    brand_model -> char list ->
    (((((char list * char list) * char list) * char list) * char list)
    list * char list) -> ergo_imp_module -> nstring -> nstring -> nstring **)

let javascript_of_module_with_dispatch bm contract_name signatures p eol quotel =
  nstring_append (QcertCodeGen.js_ast_to_javascript preamble)
    (nstring_append eol
      (nstring_append (wrapper_functions contract_name signatures eol quotel)
        (nstring_append
          (ergo_imp_module_to_javascript_top bm
            (brand_relation_brands bm.brand_model_relation) p)
          (QcertCodeGen.js_ast_to_javascript postamble))))

(** val filter_signatures :
    char list -> (char list * laergo_type_signature) list ->
    ((((char list * char list) * char list) * char list) * char list) list **)

let rec filter_signatures namespace = function
| [] -> []
| p :: rest ->
  let (fname, sig0) = p in
  if string_dec fname clause_main_name
  then filter_signatures namespace rest
  else let params = sig0.type_signature_params in
       let outtype = sig0.type_signature_output in
       let emitstype = sig0.type_signature_emits in
       (match params with
        | [] -> filter_signatures namespace rest
        | p0 :: l ->
          let (reqparam, reqtype) = p0 in
          (match l with
           | [] ->
             (match reqtype with
              | ErgoTypeClassRef (_, reqname) ->
                (match outtype with
                 | Some e ->
                   (match e with
                    | ErgoTypeClassRef (_, outname) ->
                      (match emitstype with
                       | Some e0 ->
                         (match e0 with
                          | ErgoTypeClassRef (_, emitsname) ->
                            ((((fname, reqparam), reqname), outname),
                              emitsname) :: (filter_signatures namespace rest)
                          | _ -> filter_signatures namespace rest)
                       | None ->
                         ((((fname, reqparam), reqname), outname),
                           default_event_absolute_name) :: (filter_signatures
                                                             namespace rest))
                    | _ -> filter_signatures namespace rest)
                 | None -> filter_signatures namespace rest)
              | _ -> filter_signatures namespace rest)
           | _ :: _ -> filter_signatures namespace rest))

(** val filter_signatures_with_state :
    char list -> laergo_type option -> (char list * (provenance,
    absolute_name) ergo_type_signature) list ->
    ((((char list * char list) * char list) * char list) * char list)
    list * char list **)

let filter_signatures_with_state namespace contract_state_type sigs =
  match contract_state_type with
  | Some l ->
    (match l with
     | ErgoTypeClassRef (_, statename) ->
       ((filter_signatures namespace sigs), statename)
     | _ -> ([], []))
  | None -> ((filter_signatures namespace sigs), default_state_absolute_name)

(** val ergo_imp_module_to_es6 :
    brand_model -> char list -> (provenance, absolute_name) ergo_type option
    -> (char list * (provenance, absolute_name) ergo_type_signature) list ->
    ergo_imp_module -> QcertCodeGen.ejavascript **)

let ergo_imp_module_to_es6 bm contract_name contract_state_type sigs p =
  javascript_of_module_with_dispatch bm contract_name
    (filter_signatures_with_state p.modulei_namespace contract_state_type
      sigs) p neol_newline nquotel_double
