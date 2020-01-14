open BinaryOperators
open Datatypes
open DateTimeComponent
open Ergo
open ErgoC
open ErgoType
open List0
open MathComponent
open MonetaryAmountComponent
open Names
open Provenance
open QcertData
open UnaryOperators
open UriComponent

(** val empty_sigc : char list list -> provenance -> sigc **)

let empty_sigc params prov =
  { sigc_params = (map (fun x -> (x, (ErgoTypeAny prov))) params);
    sigc_output = (Some (ErgoTypeUnit prov)) }

(** val mk_naked_closure :
    char list list -> ergoc_expr -> provenance -> ergoc_function **)

let mk_naked_closure params body prov =
  { functionc_annot = prov; functionc_sig = (empty_sigc params prov);
    functionc_body = (Some body) }

(** val mk_unary : QLib.QcertOps.Unary.op -> provenance -> ergoc_function **)

let mk_unary op0 prov =
  mk_naked_closure (('p'::('0'::[])) :: []) (EUnaryBuiltin (prov, op0, (EVar
    (prov, ('p'::('0'::[])))))) prov

(** val mk_binary_expr : ergoc_expr -> provenance -> ergoc_function **)

let mk_binary_expr e prov =
  mk_naked_closure (('p'::('1'::[])) :: (('p'::('2'::[])) :: [])) e prov

(** val mk_binary :
    QLib.QcertOps.Binary.op -> provenance -> ergoc_function **)

let mk_binary op0 prov =
  mk_binary_expr (EBinaryBuiltin (prov, op0, (EVar (prov, ('p'::('1'::[])))),
    (EVar (prov, ('p'::('2'::[])))))) prov

type ergo_stdlib_table = (char list * (provenance -> ergoc_function)) list

(** val backend_compose_table :
    ergo_stdlib_table -> ergo_stdlib_table -> ergo_stdlib_table **)

let backend_compose_table =
  app

(** val foreign_unary_operator_table : ergo_stdlib_table **)

let foreign_unary_operator_table =
  (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('d'::('o'::('u'::('b'::('l'::('e'::('O'::('p'::('t'::[]))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_float_of_string))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('c'::('o'::('s'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_acos))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('s'::('i'::('n'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_asin))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('t'::('a'::('n'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_atan))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('c'::('o'::('s'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_cos))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('c'::('o'::('s'::('h'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_cosh))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('s'::('i'::('n'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_sin))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('s'::('i'::('n'::('h'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_sinh))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('a'::('n'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_tan))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('a'::('n'::('h'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_math_op Coq_uop_math_tanh))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_format_from_string))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::[]))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_from_string))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('S'::('e'::('c'::('o'::('n'::('d'::[])))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_seconds))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('M'::('i'::('n'::('u'::('t'::('e'::[])))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_minutes))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('H'::('o'::('u'::('r'::[])))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_hours))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('D'::('a'::('y'::[]))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op Coq_uop_date_time_get_days))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('W'::('e'::('e'::('k'::[])))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_weeks))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('M'::('o'::('n'::('t'::('h'::[]))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_months))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_quarters))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('g'::('e'::('t'::('Y'::('e'::('a'::('r'::[])))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_get_years))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('S'::('e'::('c'::('o'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_from_seconds))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('M'::('i'::('n'::('u'::('t'::('e'::('s'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_from_minutes))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('H'::('o'::('u'::('r'::('s'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_from_hours))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('D'::('a'::('y'::('s'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_from_days))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('W'::('e'::('e'::('k'::('s'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_from_weeks))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('A'::('m'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_duration_amount))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('p'::('e'::('r'::('i'::('o'::('d'::('D'::('a'::('y'::('s'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_period_from_days))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('p'::('e'::('r'::('i'::('o'::('d'::('W'::('e'::('e'::('k'::('s'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_period_from_weeks))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('p'::('e'::('r'::('i'::('o'::('d'::('M'::('o'::('n'::('t'::('h'::('s'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_period_from_months))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('p'::('e'::('r'::('i'::('o'::('d'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_period_from_quarters))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('p'::('e'::('r'::('i'::('o'::('d'::('Y'::('e'::('a'::('r'::('s'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_period_from_years))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('t'::('a'::('r'::('t'::('O'::('f'::('D'::('a'::('y'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_start_of_day))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('t'::('a'::('r'::('t'::('O'::('f'::('W'::('e'::('e'::('k'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_start_of_week))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('t'::('a'::('r'::('t'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_start_of_month))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('t'::('a'::('r'::('t'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_start_of_quarter))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('t'::('a'::('r'::('t'::('O'::('f'::('Y'::('e'::('a'::('r'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_start_of_year))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('e'::('n'::('d'::('O'::('f'::('D'::('a'::('y'::[]))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_end_of_day))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('e'::('n'::('d'::('O'::('f'::('W'::('e'::('e'::('k'::[])))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_end_of_week))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('e'::('n'::('d'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_end_of_month))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('e'::('n'::('d'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_end_of_quarter))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('e'::('n'::('d'::('O'::('f'::('Y'::('e'::('a'::('r'::[])))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op
        Coq_uop_date_time_end_of_year))))) :: []))))))))))))))))))))))))))))))))))))))))

(** val foreign_binary_operator_table : ergo_stdlib_table **)

let foreign_binary_operator_table =
  (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('t'::('a'::('n'::('2'::[]))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary (Obj.magic Coq_enhanced_binary_math_op)))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('f'::('o'::('r'::('m'::('a'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op Coq_bop_date_time_format))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('a'::('d'::('d'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[])))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op Coq_bop_date_time_add))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op
        Coq_bop_date_time_subtract))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('a'::('d'::('d'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::('P'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op
        Coq_bop_date_time_add_period))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('s'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::('P'::('e'::('r'::('i'::('o'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op
        Coq_bop_date_time_subtract_period))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('i'::('s'::('S'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op Coq_bop_date_time_is_same))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('i'::('s'::('B'::('e'::('f'::('o'::('r'::('e'::[]))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op
        Coq_bop_date_time_is_before))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('i'::('s'::('A'::('f'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op
        Coq_bop_date_time_is_after))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('i'::('f'::('f'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[]))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_date_time_op Coq_bop_date_time_diff))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('A'::('m'::('o'::('u'::('n'::('t'::('F'::('o'::('r'::('m'::('a'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_monetary_amount_op
        Coq_bop_monetary_amount_format))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('C'::('o'::('d'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::('I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpForeignBinary
      (Obj.magic (Coq_enhanced_binary_monetary_amount_op
        Coq_bop_monetary_code_format))))) :: [])))))))))))

(** val foreign_table : ergo_stdlib_table **)

let foreign_table =
  backend_compose_table foreign_unary_operator_table
    foreign_binary_operator_table

(** val unary_operator_table : ergo_stdlib_table **)

let unary_operator_table =
  (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('g'::('S'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary (Obj.magic Coq_enhanced_unary_log_op)))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('o'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary OpToString)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('o'::('T'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary OpToText)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary OpLength)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('e'::('n'::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_uri_op Coq_uop_uri_encode))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('d'::('e'::('c'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_uri_op Coq_uop_uri_decode))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('A'::('b'::('s'::[])))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatAbs))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('L'::('o'::('g'::('2'::[]))))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatLog2))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('S'::('q'::('r'::('t'::[]))))))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatSqrt))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('T'::('o'::('D'::('o'::('u'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatOfNat)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('A'::('b'::('s'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatAbs))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('L'::('o'::('g'::('2'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatLog2))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('S'::('q'::('r'::('t'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary (OpNatUnary NatSqrt))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('T'::('o'::('D'::('o'::('u'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatOfNat)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('s'::('q'::('r'::('t'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatSqrt))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('e'::('x'::('p'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatExp))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('g'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatLog))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('g'::('1'::('0'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatLog10))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('c'::('e'::('i'::('l'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatCeil))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('f'::('l'::('o'::('o'::('r'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatFloor))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('b'::('s'::[]))))))))))))))))))))))))))))))))),
    (mk_unary (OpFloatUnary FloatAbs))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('a'::('x'::[]))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatBagMax)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('i'::('n'::[]))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatBagMin)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('v'::('e'::('r'::('a'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatMean)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('s'::('u'::('m'::[]))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatSum)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('d'::('o'::('u'::('b'::('l'::('e'::('T'::('o'::('I'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatTruncate)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('d'::('o'::('u'::('b'::('l'::('e'::('T'::('o'::('L'::('o'::('n'::('g'::[])))))))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatTruncate)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('r'::('u'::('n'::('c'::('a'::('t'::('e'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFloatTruncate)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('d'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::[])))))))))))))))))))))))))))))))))))))),
    (mk_unary OpDistinct)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))))))))))))))))),
    (mk_unary OpCount)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('f'::('l'::('a'::('t'::('t'::('e'::('n'::[]))))))))))))))))))))))))))))))))))))),
    (mk_unary OpFlatten)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('s'::('i'::('n'::('g'::('l'::('e'::('t'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))),
    (mk_unary OpSingleton)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('a'::('x'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op Coq_uop_date_time_max))))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('i'::('n'::[])))))))))))))))))))))))))))))))))),
    (mk_unary (OpForeignUnary
      (Obj.magic (Coq_enhanced_unary_date_time_op Coq_uop_date_time_min))))) :: [])))))))))))))))))))))))))))))))))

(** val binary_operator_table : ergo_stdlib_table **)

let binary_operator_table =
  (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('M'::('i'::('n'::[])))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpNatBinary NatMin))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('t'::('e'::('g'::('e'::('r'::('M'::('a'::('x'::[])))))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpNatBinary NatMax))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('M'::('i'::('n'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpNatBinary NatMin))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('l'::('o'::('n'::('g'::('M'::('a'::('x'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpNatBinary NatMax))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('i'::('n'::('P'::('a'::('i'::('r'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpFloatBinary FloatMin))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('m'::('a'::('x'::('P'::('a'::('i'::('r'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary (OpFloatBinary FloatMax))) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('r'::('r'::('a'::('y'::('A'::('d'::('d'::[])))))))))))))))))))))))))))))))))))))),
    (mk_binary OpBagUnion)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('a'::('r'::('r'::('a'::('y'::('S'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::[]))))))))))))))))))))))))))))))))))))))))))),
    (mk_binary OpBagDiff)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('i'::('n'::('A'::('r'::('r'::('a'::('y'::[]))))))))))))))))))))))))))))))))))))),
    (mk_binary OpContains)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('j'::('o'::('i'::('n'::[])))))))))))))))))))))))))))))))))),
    (mk_binary OpStringJoin)) :: [])))))))))

(** val builtin_table : ergo_stdlib_table **)

let builtin_table =
  (('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::('.'::('n'::('o'::('w'::[])))))))))))))))))))))))))),
    (fun prov ->
    mk_naked_closure [] (EVar (prov, current_time)) prov)) :: ((('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('g'::('e'::('t'::('O'::('p'::('t'::('i'::('o'::('n'::('s'::[])))))))))))))))))))))))))))))))))))))))),
    (fun prov -> mk_naked_closure [] (EVar (prov, options)) prov)) :: [])

(** val ergoc_stdlib : ergo_stdlib_table **)

let ergoc_stdlib =
  backend_compose_table foreign_table
    (backend_compose_table builtin_table
      (backend_compose_table unary_operator_table binary_operator_table))
