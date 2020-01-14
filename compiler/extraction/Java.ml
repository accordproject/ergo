open Datatypes
open Digits
open EmitUtil
open List0
open NativeString

type java = nstring

type java_json =
  nstring
  (* singleton inductive, whose constructor was mk_java_json *)

(** val from_java_json : java_json -> nstring **)

let from_java_json obj =
  obj

(** val mk_java_json_array : java_json list -> java_json **)

let mk_java_json_array l =
  nstring_append
    (nstring_quote
      ('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('c'::('r'::('e'::('a'::('t'::('e'::('J'::('s'::('o'::('n'::('A'::('r'::('r'::('a'::('y'::[])))))))))))))))))))))))))))))
    (nstring_bracket (nstring_quote ('('::[]))
      (nstring_map_concat (nstring_quote (','::(' '::[]))) from_java_json l)
      (nstring_quote (')'::[])))

(** val mk_java_json_object :
    nstring -> (nstring * java_json) list -> java_json **)

let mk_java_json_object quotel l =
  nstring_append
    (nstring_quote
      ('n'::('e'::('w'::(' '::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('J'::('s'::('o'::('n'::('O'::('b'::('j'::('e'::('c'::('t'::('B'::('u'::('i'::('l'::('d'::('e'::('r'::('('::(')'::[])))))))))))))))))))))))))))))))))))))
    (nstring_append
      (nstring_map_concat (nstring_quote []) (fun elem ->
        nstring_bracket (nstring_quote ('.'::('a'::('d'::('d'::('('::[]))))))
          (nstring_append quotel
            (nstring_append (fst elem)
              (nstring_append quotel
                (nstring_append (nstring_quote (','::(' '::[])))
                  (from_java_json (snd elem)))))) (nstring_quote (')'::[])))
        l)
      (nstring_quote
        ('.'::('t'::('o'::('J'::('s'::('o'::('n'::('O'::('b'::('j'::('e'::('c'::('t'::('('::(')'::[])))))))))))))))))

(** val mk_java_json_primitive : nstring -> java_json **)

let mk_java_json_primitive obj =
  nstring_append
    (nstring_quote
      ('n'::('e'::('w'::(' '::('J'::('s'::('o'::('n'::('P'::('r'::('i'::('m'::('i'::('t'::('i'::('v'::('e'::('('::[])))))))))))))))))))
    (nstring_append obj (nstring_quote (')'::[])))

(** val mk_java_json_string : nstring -> nstring -> java_json **)

let mk_java_json_string quotel s =
  mk_java_json_primitive (nstring_bracket quotel s quotel)

(** val java_json_NULL : java_json **)

let java_json_NULL =
  nstring_quote
    ('J'::('s'::('o'::('n'::('N'::('u'::('l'::('l'::('.'::('I'::('N'::('S'::('T'::('A'::('N'::('C'::('E'::[])))))))))))))))))

(** val mk_java_json_nat : nstring -> int -> java_json **)

let mk_java_json_nat quotel n =
  mk_java_json_object quotel
    (((nstring_quote ('$'::('n'::('a'::('t'::[]))))),
    (mk_java_json_primitive (nstring_quote (coq_Z_to_string10 n)))) :: [])

(** val mk_java_json_number : float -> java_json **)

let mk_java_json_number n =
  mk_java_json_primitive
    (nstring_quote
      ((fun x -> Util.char_list_of_string (Util.qcert_string_of_float x)) n))

(** val mk_java_json_bool : bool -> java_json **)

let mk_java_json_bool b =
  mk_java_json_primitive
    (if b
     then nstring_quote ('t'::('r'::('u'::('e'::[]))))
     else nstring_quote ('f'::('a'::('l'::('s'::('e'::[]))))))

(** val mk_java_string : nstring -> nstring **)

let mk_java_string s =
  nstring_append nquotel_double (nstring_append s nquotel_double)

(** val mk_java_call : nstring -> nstring -> java_json list -> java_json **)

let mk_java_call cname mname el =
  nstring_append cname
    (nstring_append (nstring_quote ('.'::[]))
      (nstring_append mname
        (nstring_append (nstring_quote ('('::[]))
          (nstring_append
            (nstring_concat (nstring_quote (','::(' '::[])))
              (map from_java_json el)) (nstring_quote (')'::[]))))))

(** val mk_java_unary_op0 : nstring -> java_json -> java_json **)

let mk_java_unary_op0 opname e =
  mk_java_call
    (nstring_quote
      ('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::[])))))))))))))))
    opname (e :: [])

(** val mk_java_unary_op1 : nstring -> nstring -> java_json -> java_json **)

let mk_java_unary_op1 opname s e =
  mk_java_call
    (nstring_quote
      ('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::[])))))))))))))))
    opname (s :: (e :: []))

(** val mk_java_unary_opn :
    nstring -> nstring list -> java_json -> java_json **)

let mk_java_unary_opn opname sn e =
  mk_java_call
    (nstring_quote
      ('U'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::[])))))))))))))))
    opname (app (map (fun x -> x) sn) (e :: []))

(** val mk_java_binary_op0 :
    nstring -> java_json -> java_json -> java_json **)

let mk_java_binary_op0 opname e1 e2 =
  mk_java_call
    (nstring_quote
      ('B'::('i'::('n'::('a'::('r'::('y'::('O'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::('s'::[]))))))))))))))))
    opname (e1 :: (e2 :: []))

(** val mk_java_unary_op0_foreign :
    nstring -> nstring -> java_json -> java_json **)

let mk_java_unary_op0_foreign cname opname e =
  mk_java_call cname opname (e :: [])

(** val mk_java_binary_op0_foreign :
    nstring -> nstring -> java_json -> java_json -> java_json **)

let mk_java_binary_op0_foreign cname opname e1 e2 =
  mk_java_call cname opname (e1 :: (e2 :: []))

(** val mk_java_collection : nstring -> nstring list -> nstring **)

let mk_java_collection typ s =
  nstring_append
    (nstring_quote
      ('n'::('e'::('w'::(' '::('R'::('u'::('n'::('t'::('i'::('m'::('e'::('U'::('t'::('i'::('l'::('s'::('.'::('C'::('o'::('l'::('l'::('e'::('c'::('t'::('i'::('o'::('n'::('B'::('u'::('i'::('l'::('d'::('e'::('r'::('<'::[]))))))))))))))))))))))))))))))))))))
    (nstring_append typ
      (nstring_append (nstring_quote ('>'::('('::[])))
        (nstring_append (nstring_quote (nat_to_string10 (length s)))
          (nstring_append (nstring_quote (')'::[]))
            (nstring_append
              (nstring_map_concat (nstring_quote []) (fun elem ->
                nstring_append
                  (nstring_quote ('.'::('a'::('d'::('d'::('('::[]))))))
                  (nstring_append elem (nstring_quote (')'::[])))) s)
              (nstring_quote
                ('.'::('r'::('e'::('s'::('u'::('l'::('t'::('('::(')'::[])))))))))))))))

(** val mk_java_string_collection : nstring list -> nstring **)

let mk_java_string_collection s =
  mk_java_collection
    (nstring_quote ('S'::('t'::('r'::('i'::('n'::('g'::[])))))))
    (map mk_java_string s)
