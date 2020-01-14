open Datatypes
open ErgoNNRC
open List0
open Misc
open NativeString
open QLib
open TBrandModel
open Version

(** val java_method_of_body :
    ergo_nnrc_expr -> char list -> nstring -> nstring -> QcertCodeGen.java **)

let java_method_of_body e fname eol quotel =
  let input_v = 'c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))) in
  QcertCodeGen.nnrc_expr_to_java_method input_v e (Pervasives.succ 0) eol
    quotel ((input_v, (nstring_quote input_v)) :: [])
    (nstring_quote (QcertCodeGen.java_identifier_sanitizer fname))

(** val java_method_of_nnrc_function :
    brand_model -> char list -> ergo_nnrc_lambda -> nstring -> nstring ->
    QcertCodeGen.java **)

let java_method_of_nnrc_function _ fname fbody eol quotel =
  java_method_of_body fbody.lambdan_body fname eol quotel

(** val java_methods_of_nnrc_functions :
    brand_model -> (char list * ergo_nnrc_lambda) list -> char list ->
    nstring -> nstring -> QcertCodeGen.java **)

let java_methods_of_nnrc_functions m fl _ eol quotel =
  nstring_multi_append eol (fun f ->
    java_method_of_nnrc_function m (fst f) (snd f) eol quotel) fl

(** val java_class_of_nnrc_function_table :
    brand_model -> char list -> ergo_nnrc_function_table -> nstring ->
    nstring -> QcertCodeGen.java **)

let java_class_of_nnrc_function_table m filename ft eol quotel =
  let tname = QcertCodeGen.java_identifier_sanitizer filename in
  nstring_append
    (nstring_quote
      ('p'::('u'::('b'::('l'::('i'::('c'::(' '::('c'::('l'::('a'::('s'::('s'::(' '::[]))))))))))))))
    (nstring_append (nstring_quote tname)
      (nstring_append
        (nstring_quote
          (' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::(' '::('E'::('r'::('g'::('o'::('C'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::('{'::[])))))))))))))))))))))))))))
        (nstring_append eol
          (nstring_append
            (java_methods_of_nnrc_functions m ft.function_tablen_funs tname
              eol quotel)
            (nstring_append eol
              (nstring_append (nstring_quote ('}'::[])) eol))))))

(** val preamble : nstring -> nstring **)

let preamble eol =
  nstring_append (nstring_quote [])
    (nstring_append
      (nstring_quote
        ('/'::('*'::(' '::('G'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::('d'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('e'::('r'::('g'::('o'::('c'::(' '::('v'::('e'::('r'::('s'::('i'::('o'::('n'::(' '::[]))))))))))))))))))))))))))))))))))
      (nstring_append (nstring_quote ergo_version)
        (nstring_append (nstring_quote (' '::('*'::('/'::[]))))
          (nstring_append eol
            (nstring_append
              (nstring_quote
                ('i'::('m'::('p'::('o'::('r'::('t'::(' '::('c'::('o'::('m'::('.'::('g'::('o'::('o'::('g'::('l'::('e'::('.'::('g'::('s'::('o'::('n'::('.'::('*'::(';'::[]))))))))))))))))))))))))))
              (nstring_append eol
                (nstring_append
                  (nstring_quote
                    ('i'::('m'::('p'::('o'::('r'::('t'::(' '::('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('r'::('u'::('n'::('t'::('i'::('m'::('e'::('.'::('*'::(';'::[])))))))))))))))))))))))))))))))))))))))))
                  eol)))))))

(** val java_of_declaration :
    brand_model -> char list -> ergo_nnrc_declaration -> int -> int ->
    nstring -> nstring -> (QcertCodeGen.java * QcertCodeGen.java_data) * int **)

let java_of_declaration m filename s t _ eol quotel =
  match s with
  | DNFunc (_, _) ->
    (((nstring_quote []), (QcertCodeGen.mk_java_data (nstring_quote []))), t)
  | DNFuncTable (_, ft) ->
    (((java_class_of_nnrc_function_table m filename ft eol quotel),
      (QcertCodeGen.mk_java_data
        (nstring_quote ('n'::('u'::('l'::('l'::[]))))))), t)

(** val java_of_declarations :
    brand_model -> char list -> ergo_nnrc_declaration list -> int -> int ->
    nstring -> nstring -> QcertCodeGen.java **)

let java_of_declarations m filename sl t i eol quotel =
  let proc_one = fun s acc ->
    let (s0, t0) = acc in
    let (p, t1) = java_of_declaration m filename s t0 i eol quotel in
    let (s1, _) = p in ((nstring_append s0 s1), t1)
  in
  let (sn, _) = fold_right proc_one ((nstring_quote []), t) sl in sn

(** val nnrc_module_to_java :
    brand_model -> char list -> ergo_nnrc_module -> nstring -> nstring ->
    QcertCodeGen.java **)

let nnrc_module_to_java m filename p eol quotel =
  nstring_append (preamble eol)
    (nstring_append eol
      (java_of_declarations m filename p.modulen_declarations 0 0 eol quotel))

(** val nnrc_module_to_java_top :
    brand_model -> char list -> ergo_nnrc_module -> QcertCodeGen.java **)

let nnrc_module_to_java_top m filename p =
  nnrc_module_to_java m filename p QcertCodeGen.eeol_newline
    QcertCodeGen.equotel_double
