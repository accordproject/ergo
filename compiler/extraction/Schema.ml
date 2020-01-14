open Bindings
open BrandRelation
open CoqLibAdd
open DataResult
open ForeignData
open ForeignType
open TBrandContext
open TBrandModel

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val mk_brand_relation :
    foreign_data -> (char list * char list) list -> brand_relation qresult **)

let mk_brand_relation fdata br =
  if brand_relation_trans_dec br
  then if brand_relation_assym_dec br
       then qsuccess fdata br
       else qfailure fdata (CompilationError
              ('B'::('r'::('a'::('n'::('d'::(' '::('r'::('e'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::('s'::('s'::('y'::('m'::('e'::('t'::('r'::('i'::('c'::[])))))))))))))))))))))))))))))))))
  else qfailure fdata (CompilationError
         ('B'::('r'::('a'::('n'::('d'::(' '::('r'::('e'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('t'::('r'::('a'::('n'::('s'::('i'::('t'::('i'::('v'::('e'::[])))))))))))))))))))))))))))))))))

(** val mk_brand_context :
    foreign_type -> brand_relation -> brand_context_decls -> brand_context **)

let mk_brand_context _ _ bcds =
  rec_sort coq_ODT_string bcds

(** val make_brand_model_from_decls_fails :
    foreign_data -> foreign_type -> brand_relation -> brand_context_decls ->
    brand_model qresult **)

let make_brand_model_from_decls_fails fdata ftype b bcds =
  let m = mk_brand_context ftype b bcds in
  let h = fun _ -> make_brand_model ftype b m in
  let b0 = is_true (brand_model_domain_dec ftype b m) in
  if b0
  then let b1 = is_true (brand_model_subtype_weak_dec ftype b m) in
       if b1
       then let h0 = h __ in qsuccess fdata h0
       else qfailure fdata (CompilationError
              ('S'::('u'::('b'::('t'::('y'::('p'::('i'::('n'::('g'::(' '::('v'::('i'::('o'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::(' '::('b'::('r'::('a'::('n'::('d'::(' '::('m'::('o'::('d'::('e'::('l'::[])))))))))))))))))))))))))))))))))))
  else qfailure fdata (CompilationError
         ('B'::('r'::('a'::('n'::('d'::(' '::('w'::('i'::('t'::('h'::('o'::('u'::('t'::(' '::('a'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('i'::('n'::(' '::('b'::('r'::('a'::('n'::('d'::(' '::('m'::('o'::('d'::('e'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))
