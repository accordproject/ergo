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

(** val esuccess : 'a1 -> ewarning list -> 'a1 eresult **)

let esuccess a l =
  Success (a, l)

(** val efailure : eerror -> 'a1 eresult **)

let efailure e =
  Failure e

(** val eolift : ('a1 -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult **)

let eolift f a =
  lift_failure (fun xw ->
    let (x, w) = xw in
    lift_failure_in (fun xw' -> let (x', w') = xw' in (x', (app w w'))) (f x))
    a

(** val eolift_warning :
    (('a1 * ewarning list) -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult **)

let eolift_warning =
  lift_failure

(** val elift : ('a1 -> 'a2) -> 'a1 eresult -> 'a2 eresult **)

let elift f a =
  lift_failure_in (fun xw -> let (x, w) = xw in ((f x), w)) a

(** val elift2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult **)

let elift2 f a b =
  eolift (fun x -> elift (fun y -> f x y) b) a

(** val elift3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult
    -> 'a4 eresult **)

let elift3 f a b c =
  eolift (fun x -> elift2 (fun y z -> f x y z) b c) a

(** val elift_fold_left :
    ('a1 -> 'a2 -> 'a1 eresult) -> 'a2 list -> 'a1 -> 'a1 eresult **)

let elift_fold_left f l a =
  let proc_one = fun acc x -> eolift (fun acc0 -> f acc0 x) acc in
  fold_left proc_one l (esuccess a [])

(** val emaplift : ('a1 -> 'a2 eresult) -> 'a1 list -> 'a2 list eresult **)

let emaplift f al =
  let init_bl = Success ([], []) in
  let proc_one = fun acc a ->
    elift2 (fun acc0 x -> app acc0 (x :: [])) acc (f a)
  in
  fold_left proc_one al init_bl

(** val elift_context_fold_left :
    ('a3 -> 'a1 -> ('a2 * 'a3) eresult) -> 'a1 list -> 'a3 -> ('a2
    list * 'a3) eresult **)

let elift_context_fold_left f l c =
  elift_fold_left (fun acc c0 ->
    elift (fun mc -> ((app (fst acc) ((fst mc) :: [])), (snd mc)))
      (f (snd acc) c0)) l ([], c)

(** val eflatmaplift :
    ('a1 -> 'a2 list eresult) -> 'a1 list -> 'a2 list eresult **)

let eflatmaplift f al =
  elift_fold_left (fun acc c -> elift (fun mc -> app acc mc) (f c)) al []

(** val eresult_of_option :
    'a1 option -> eerror -> ewarning list -> 'a1 eresult **)

let eresult_of_option a e warnings =
  result_of_option (lift (fun x -> (x, warnings)) a) e

(** val eolift2 :
    ('a1 -> 'a2 -> 'a3 eresult) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult **)

let eolift2 f a b =
  eolift id (elift2 f a b)

(** val elift_maybe :
    ('a1 -> 'a1 eresult option) -> 'a1 eresult -> 'a1 eresult **)

let elift_maybe f a =
  eolift (fun x -> match x with
                   | Some s -> s
                   | None -> a) (elift f a)

(** val elift_fail : (eerror -> 'a1 eresult) -> 'a1 eresult -> 'a1 eresult **)

let elift_fail g a = match a with
| Success _ -> a
| Failure e -> g e

(** val elift_both : ('a1 -> 'a2) -> (eerror -> 'a2) -> 'a1 eresult -> 'a2 **)

let elift_both f g = function
| Success p -> let (s, _) = p in f s
| Failure e -> g e

(** val elift2_both :
    ('a1 -> 'a2 -> 'a3) -> (eerror -> 'a3) -> 'a1 eresult -> 'a2 eresult ->
    'a3 **)

let elift2_both f g a b =
  match a with
  | Success p ->
    let (s1, _) = p in
    (match b with
     | Success p0 -> let (s2, _) = p0 in f s1 s2
     | Failure e -> g e)
  | Failure e -> g e

(** val eerror_of_qerror : provenance -> qerror -> eerror **)

let eerror_of_qerror prov = function
| CompilationError msg -> ECompilationError (prov, msg)
| TypeError msg -> ETypeError (prov, msg)
| UserError _ ->
  ESystemError (prov,
    ('U'::('s'::('e'::('r'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('c'::('c'::('u'::('r'::('e'::('d'::(' '::('i'::('n'::(' '::('b'::('a'::('c'::('k'::('e'::('n'::('d'::[]))))))))))))))))))))))))))))))

(** val eresult_of_qresult : provenance -> 'a1 qresult -> 'a1 eresult **)

let eresult_of_qresult prov = function
| Success s -> esuccess s []
| Failure e -> efailure (eerror_of_qerror prov e)

(** val format_error : char list -> provenance -> char list -> char list **)

let format_error name prov msg =
  let loc = loc_of_provenance prov in
  append name
    (append (' '::('a'::('t'::(' '::[]))))
      (append (string_of_location_no_file loc)
        (append (' '::('\''::[])) (append msg ('\''::[])))))

(** val clause_call_not_on_contract_error : provenance -> 'a1 eresult **)

let clause_call_not_on_contract_error prov =
  efailure (ECompilationError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('a'::('l'::('l'::(' '::('a'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::(' '::('e'::('x'::('c'::('e'::('p'::('t'::(' '::('o'::('n'::(' '::('\''::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::('\''::[])))))))))))))))))))))))))))))))))))))))))))

(** val use_contract_not_in_contract_error : provenance -> 'a1 eresult **)

let use_contract_not_in_contract_error prov =
  efailure (ECompilationError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('u'::('s'::('e'::(' '::('\''::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::('\''::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val call_clause_not_in_contract_error :
    provenance -> char list -> 'a1 eresult **)

let call_clause_not_in_contract_error prov clname =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('a'::('l'::('l'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::(' '::[])))))))))))))))))))
      (append clname
        (' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[]))))))))))))))))))))))))))

(** val not_in_clause_error : provenance -> 'a1 eresult **)

let not_in_clause_error prov =
  efailure (ECompilationError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('u'::('s'::('e'::(' '::('\''::('c'::('l'::('a'::('u'::('s'::('e'::('\''::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('o'::('u'::('t'::('s'::('i'::('d'::('e'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))

(** val case_option_not_on_either_error : provenance -> 'a1 eresult **)

let case_option_not_on_either_error prov =
  efailure (ECompilationError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('u'::('n'::('l'::('e'::('s'::('s'::(' '::('a'::('g'::('a'::('i'::('n'::('s'::('t'::(' '::('a'::('n'::(' '::('o'::('p'::('t'::('i'::('o'::('n'::(' '::('t'::('y'::('p'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))

(** val set_state_on_non_brand_error :
    provenance -> char list -> 'a1 eresult **)

let set_state_on_non_brand_error prov name =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('u'::('s'::('e'::(' '::('\''::('s'::('e'::('t'::(' '::('s'::('t'::('a'::('t'::('e'::('.'::[]))))))))))))))))))))))
      (append name
        (' '::('o'::('n'::(' '::('n'::('o'::('n'::('-'::('o'::('b'::('j'::('e'::('t'::(' '::('s'::('t'::('a'::('t'::('e'::[])))))))))))))))))))))))

(** val import_not_found_error : provenance -> char list -> 'a1 eresult **)

let import_not_found_error prov import =
  efailure (ECompilationError (prov,
    (append
      ('I'::('m'::('p'::('o'::('r'::('t'::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(':'::(' '::[]))))))))))))))))))
      import)))

(** val type_name_not_found_error : provenance -> char list -> 'a1 eresult **)

let type_name_not_found_error prov ln =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))))))))))
      (append ln ('\''::[])))))

(** val namespace_not_found_error : provenance -> char list -> 'a1 eresult **)

let namespace_not_found_error prov ns =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('n'::('a'::('m'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('\''::[])))))))))))))))))))))))
      (append ns ('\''::[])))))

(** val variable_name_not_found_error :
    provenance -> char list -> 'a1 eresult **)

let variable_name_not_found_error prov ln =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))))))))))))))
      (append ln ('\''::[])))))

(** val enum_name_not_found_error : provenance -> char list -> 'a1 eresult **)

let enum_name_not_found_error prov ln =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('e'::('n'::('u'::('m'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))))))))))
      (append ln ('\''::[])))))

(** val function_name_not_found_error :
    provenance -> char list -> 'a1 eresult **)

let function_name_not_found_error prov ln =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))))))))))))))
      (append ln ('\''::[])))))

(** val contract_name_not_found_error :
    provenance -> char list -> 'a1 eresult **)

let contract_name_not_found_error prov ln =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))))))))))))))
      (append ln ('\''::[])))))

(** val import_name_not_found_error :
    provenance -> char list -> char list -> 'a1 eresult **)

let import_name_not_found_error prov namespace name_ref =
  efailure (ECompilationError (prov,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('i'::('m'::('p'::('o'::('r'::('t'::(' '::('n'::('a'::('m'::('e'::(' '::('\''::[]))))))))))))))))))))
      (append name_ref
        (append
          ('\''::(' '::('i'::('n'::(' '::('C'::('T'::('O'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('a'::('m'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::[]))))))))))))))))))))))))
          namespace)))))

(** val main_parameter_mismatch_error : provenance -> 'a1 eresult **)

let main_parameter_mismatch_error prov =
  efailure (ECompilationError (prov,
    ('P'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('d'::('u'::('r'::('i'::('n'::('g'::(' '::('m'::('a'::('i'::('n'::(' '::('c'::('r'::('e'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))))))))

(** val main_at_least_one_parameter_error : provenance -> 'a1 eresult **)

let main_at_least_one_parameter_error prov =
  efailure (ECompilationError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('r'::('e'::('a'::('t'::('e'::(' '::('m'::('a'::('i'::('n'::(' '::('i'::('f'::(' '::('n'::('o'::('t'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('o'::('n'::('e'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))))

(** val function_not_found_error : provenance -> char list -> 'a1 eresult **)

let function_not_found_error prov fname =
  efailure (ECompilationError (prov,
    (append
      ('F'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('\''::[]))))))))))
      (append fname
        ('\''::(' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))

(** val call_params_error : provenance -> char list -> 'a1 eresult **)

let call_params_error prov fname =
  efailure (ECompilationError (prov,
    (append
      ('P'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(' '::('w'::('h'::('e'::('n'::(' '::('c'::('a'::('l'::('l'::('i'::('n'::('g'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('\''::[]))))))))))))))))))))))))))))))))))))))))))
      (append fname ('\''::[])))))

(** val eval_unary_operator_error :
    provenance -> ergo_unary_operator -> 'a1 eresult **)

let eval_unary_operator_error prov op0 =
  let op_name = toString coq_ToString_ergo_unary_operator op0 in
  efailure (ESystemError (prov,
    (append
      ('U'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('['::[])))))))))))))))))))))
      (append op_name
        (']'::(' '::('d'::('u'::('r'::('i'::('n'::('g'::(' '::('e'::('v'::('a'::('l'::(' '::('('::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('s'::('o'::('l'::('v'::('e'::('d'::(')'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))

(** val eval_binary_operator_error :
    provenance -> ergo_binary_operator -> 'a1 eresult **)

let eval_binary_operator_error prov op0 =
  let op_name = toString coq_ToString_ergo_binary_operator op0 in
  efailure (ESystemError (prov,
    (append
      ('U'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('['::[])))))))))))))))))))))
      (append op_name
        (']'::(' '::('d'::('u'::('r'::('i'::('n'::('g'::(' '::('e'::('v'::('a'::('l'::(' '::('('::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('s'::('o'::('l'::('v'::('e'::('d'::(')'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))

(** val eval_unary_builtin_error :
    provenance -> QLib.QcertOps.Unary.op -> 'a1 eresult **)

let eval_unary_builtin_error prov op0 =
  let op_name =
    toString
      (coq_ToString_unary_op enhanced_foreign_data enhanced_foreign_operators)
      op0
  in
  efailure (ERuntimeError (prov,
    (append
      ('E'::('v'::('a'::('l'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('o'::('r'::(' '::('b'::('u'::('i'::('l'::('t'::('i'::('n'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('['::[])))))))))))))))))))))))))))))))))))))))
      (append op_name
        (']'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::('.'::[])))))))))))))

(** val eval_binary_builtin_error :
    provenance -> QLib.QcertOps.Binary.op -> 'a1 eresult **)

let eval_binary_builtin_error prov op0 =
  let op_name =
    toString
      (coq_ToString_binary_op enhanced_foreign_data
        enhanced_foreign_operators) op0
  in
  efailure (ERuntimeError (prov,
    (append
      ('E'::('v'::('a'::('l'::('u'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('o'::('r'::(' '::('b'::('u'::('i'::('l'::('t'::('i'::('n'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('['::[]))))))))))))))))))))))))))))))))))))))))
      (append op_name
        (']'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::('.'::[])))))))))))))

(** val eval_if_not_boolean_error : provenance -> 'a1 eresult **)

let eval_if_not_boolean_error prov =
  efailure (ERuntimeError (prov,
    ('\''::('I'::('f'::('\''::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('b'::('o'::('o'::('l'::('e'::('a'::('n'::('.'::[])))))))))))))))))))))))))))))

(** val eval_foreach_not_on_array_error : provenance -> 'a1 eresult **)

let eval_foreach_not_on_array_error prov =
  efailure (ERuntimeError (prov,
    ('F'::('o'::('r'::('e'::('a'::('c'::('h'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('c'::('a'::('l'::('l'::('e'::('d'::(' '::('o'::('n'::(' '::('a'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::[]))))))))))))))))))))))))))))))))))))))))

(** val template_type_not_found_error : provenance -> 'a1 eresult **)

let template_type_not_found_error prov =
  efailure (ERuntimeError (prov,
    ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('t'::('e'::('m'::('p'::('l'::('a'::('t'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('('::('o'::('n'::('e'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('e'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('e'::('x'::('t'::('e'::('n'::('d'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('A'::('c'::('c'::('c'::('o'::('r'::('d'::('C'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::('o'::('r'::(' '::('A'::('c'::('c'::('o'::('r'::('d'::('C'::('l'::('a'::('u'::('s'::('e'::(')'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val more_than_one_template_type_error :
    provenance -> char list -> 'a1 eresult **)

let more_than_one_template_type_error prov msg =
  efailure (ERuntimeError (prov,
    (append
      ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('t'::('e'::('m'::('p'::('l'::('a'::('t'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('('::('a'::('t'::(' '::('m'::('o'::('s'::('t'::(' '::('o'::('n'::('e'::(' '::('o'::('f'::(' '::[])))))))))))))))))))))))))))))))))))))))
      (append msg
        (' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('e'::('x'::('t'::('e'::('n'::('d'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('A'::('c'::('c'::('c'::('o'::('r'::('d'::('C'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::('o'::('r'::(' '::('A'::('c'::('c'::('o'::('r'::('d'::('C'::('l'::('a'::('u'::('s'::('e'::(')'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val no_ergo_module_error : provenance -> 'a1 eresult **)

let no_ergo_module_error prov =
  efailure (ESystemError (prov,
    ('N'::('o'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('e'::('r'::('g'::('o'::(' '::('f'::('o'::('u'::('n'::('d'::[])))))))))))))))))))))

(** val built_in_function_not_found_error :
    provenance -> char list -> 'a1 eresult **)

let built_in_function_not_found_error prov fname =
  efailure (ESystemError (prov,
    (append
      ('B'::('u'::('i'::('l'::('t'::(' '::('i'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))))))))))
      (append fname
        (' '::('n'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::[]))))))))))))))

(** val built_in_function_without_body_error :
    provenance -> char list -> 'a1 eresult **)

let built_in_function_without_body_error prov fname =
  efailure (ESystemError (prov,
    (append
      ('B'::('u'::('i'::('l'::('t'::(' '::('i'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))))))))))
      (append fname
        (' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('h'::('a'::('v'::('e'::(' '::('a'::(' '::('b'::('o'::('d'::('y'::[])))))))))))))))))))))))))

(** val enforce_error_content :
    provenance -> char list -> QLib.QcertData.data **)

let enforce_error_content prov msg =
  let message =
    format_error
      ('E'::('n'::('f'::('o'::('r'::('c'::('e'::(' '::('E'::('r'::('r'::('o'::('r'::[])))))))))))))
      prov msg
  in
  Coq_dbrand ((default_error_absolute_name :: []), (Coq_drec
  ((('m'::('e'::('s'::('s'::('a'::('g'::('e'::[]))))))), (Coq_dstring
  message)) :: [])))

(** val default_match_error_content : provenance -> data **)

let default_match_error_content _ =
  let message =
    'D'::('i'::('s'::('p'::('a'::('t'::('c'::('h'::(' '::('E'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::('m'::('a'::('t'::('c'::('h'::('e'::('s'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  Coq_dbrand ((default_error_absolute_name :: []), (Coq_drec
  ((('m'::('e'::('s'::('s'::('a'::('g'::('e'::[]))))))), (Coq_dstring
  message)) :: [])))

(** val should_have_one_contract_error : provenance -> 'a1 eresult **)

let should_have_one_contract_error prov =
  efailure (ECompilationError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('o'::('n'::('e'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[]))))))))))))))))))))))))))))))))))

(** val this_in_calculus_error : provenance -> 'a1 eresult **)

let this_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('t'::('h'::('i'::('s'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))

(** val contract_in_calculus_error : provenance -> 'a1 eresult **)

let contract_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))

(** val clause_in_calculus_error : provenance -> 'a1 eresult **)

let clause_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('c'::('l'::('a'::('u'::('s'::('e'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))))

(** val operator_in_calculus_error : provenance -> 'a1 eresult **)

let operator_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('a'::('n'::(' '::('o'::('v'::('e'::('r'::('l'::('o'::('a'::('d'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val state_in_calculus_error : provenance -> 'a1 eresult **)

let state_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('s'::('t'::('a'::('t'::('e'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[]))))))))))))))))))))))))))))))))))))))))))

(** val text_in_calculus_error : provenance -> 'a1 eresult **)

let text_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('{'::('{'::(' '::('t'::('e'::('x'::('t'::(' '::('}'::('}'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))

(** val complex_foreach_in_calculus_error : provenance -> 'a1 eresult **)

let complex_foreach_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('o'::('n'::('l'::('y'::(' '::('h'::('a'::('v'::('e'::(' '::('s'::('i'::('n'::('g'::('l'::('e'::(' '::('l'::('o'::('o'::('p'::(' '::('f'::('o'::('r'::('e'::('a'::('c'::('h'::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val print_in_calculus_error : provenance -> 'a1 eresult **)

let print_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('p'::('r'::('i'::('n'::('t'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[]))))))))))))))))))))))))))))))))))))))))))

(** val function_not_inlined_error :
    provenance -> char list -> char list -> 'a1 eresult **)

let function_not_inlined_error prov msg fname =
  efailure (ESystemError (prov,
    (append ('['::[])
      (append msg
        (append (']'::(' '::[]))
          (append
            ('F'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[])))))))))
            (append fname
              (' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('g'::('e'::('t'::(' '::('i'::('n'::('l'::('i'::('n'::('e'::('d'::[])))))))))))))))))))))))))))

(** val function_in_group_not_inlined_error :
    provenance -> char list -> char list -> 'a1 eresult **)

let function_in_group_not_inlined_error prov gname fname =
  efailure (ESystemError (prov,
    (append ('C'::('l'::('a'::('u'::('s'::('e'::(' '::[])))))))
      (append fname
        (append
          (' '::('i'::('n'::(' '::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::(' '::[])))))))))))))
          (append gname
            (' '::('d'::('i'::('d'::(' '::('n'::('o'::('t'::(' '::('g'::('e'::('t'::(' '::('i'::('n'::('l'::('i'::('n'::('e'::('d'::[]))))))))))))))))))))))))))

(** val as_in_calculus_error : provenance -> 'a1 eresult **)

let as_in_calculus_error prov =
  efailure (ESystemError (prov,
    ('S'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('f'::('i'::('n'::('d'::(' '::('\''::('a'::('s'::('\''::(' '::('i'::('n'::(' '::('E'::('r'::('g'::('o'::(' '::('C'::('a'::('l'::('c'::('u'::('l'::('u'::('s'::[])))))))))))))))))))))))))))))))))))))))

(** val no_duplicates_with_err :
    char list list -> 'a1 -> (char list option -> eerror) -> 'a1 eresult **)

let no_duplicates_with_err l succ err =
  if coq_NoDup_dec string_dec l
  then esuccess succ []
  else let s = find_duplicate l in efailure (err s)

(** val duplicate_function_params_error :
    provenance -> char list -> char list option -> eerror **)

let duplicate_function_params_error prov fname = function
| Some vname0 ->
  ECompilationError (prov,
    (append
      ('V'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('\''::[]))))))))))
      (append vname0
        (append
          ('\''::(' '::('i'::('s'::(' '::('b'::('o'::('u'::('n'::('d'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('t'::('i'::('m'::('e'::('s'::(' '::('i'::('n'::(' '::('\''::[]))))))))))))))))))))))))))))))
          (append fname ('\''::[]))))))
| None ->
  ECompilationError (prov,
    (append
      ('S'::('a'::('m'::('e'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('b'::('o'::('u'::('n'::('d'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('t'::('i'::('m'::('e'::('s'::(' '::('i'::('n'::(' '::('\''::[])))))))))))))))))))))))))))))))))))))))
      (append fname ('\''::[]))))

(** val duplicate_function_params_check :
    provenance -> char list -> char list list -> 'a1 -> 'a1 eresult **)

let duplicate_function_params_check prov fname l succ =
  no_duplicates_with_err l succ (duplicate_function_params_error prov fname)

(** val duplicate_clause_for_request_error :
    provenance -> char list option -> eerror **)

let duplicate_clause_for_request_error prov = function
| Some rname0 ->
  ECompilationError (prov,
    (append
      ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::('s'::(' '::('c'::('a'::('n'::(' '::('p'::('r'::('o'::('c'::('e'::('s'::('s'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::(' '::('\''::[]))))))))))))))))))))))))))))))))))))))))))
      (append rname0 ('\''::[]))))
| None ->
  ECompilationError (prov,
    ('M'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('c'::('l'::('a'::('u'::('s'::('e'::('s'::(' '::('c'::('a'::('n'::(' '::('p'::('r'::('o'::('c'::('e'::('s'::('s'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))

(** val duplicate_clause_for_request_check :
    provenance -> char list list -> 'a1 -> 'a1 eresult **)

let duplicate_clause_for_request_check prov l succ =
  no_duplicates_with_err l succ (duplicate_clause_for_request_error prov)

(** val warning_no_else : provenance -> ewarning **)

let warning_no_else prov =
  EWarning (prov,
    ('N'::('o'::(' '::('e'::('l'::('s'::('e'::(' '::('i'::('n'::(' '::('e'::('n'::('f'::('o'::('r'::('c'::('e'::[])))))))))))))))))))

(** val warning_global_shadowing : provenance -> char list -> ewarning **)

let warning_global_shadowing prov name =
  EWarning (prov,
    (append ('C'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::[])))))))))
      (append name
        (' '::('h'::('i'::('d'::('e'::('s'::(' '::('a'::('n'::(' '::('e'::('x'::('i'::('s'::('t'::('i'::('n'::('g'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('w'::('i'::('t'::('h'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('n'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))

type result_file = { res_contract_name : char list option;
                     res_file : char list; res_content : nstring }
