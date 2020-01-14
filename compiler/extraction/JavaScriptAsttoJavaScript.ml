open Ascii
open FloatAdd
open JavaScript
open JavaScriptAst
open JsNumber
open JsSyntax
open List0
open Nat
open NativeString

(** val eol : nstring **)

let eol =
  nstring_quote
    ((ascii_of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))::[])

(** val quotel : nstring **)

let quotel =
  nstring_quote ('"'::[])

(** val indent : int -> nstring **)

let rec indent i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> nstring_quote [])
    (fun j -> nstring_append (nstring_quote (' '::(' '::[]))) (indent j))
    i

(** val comma_list_string : char list list -> nstring **)

let comma_list_string l =
  nstring_concat (nstring_quote (','::(' '::[]))) (map nstring_quote l)

(** val comma_list : nstring list -> nstring **)

let comma_list l =
  nstring_concat (nstring_quote (','::(' '::[]))) l

(** val js_quote_char : char -> nstring **)

let js_quote_char a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then nstring_quote (a::[])
         else if b1
              then if b2
                   then if b3
                        then nstring_quote (a::[])
                        else if b4
                             then nstring_quote (a::[])
                             else if b5
                                  then nstring_quote (a::[])
                                  else if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('r'::[]))
                   else nstring_quote (a::[])
              else if b2
                   then if b3
                        then nstring_quote (a::[])
                        else if b4
                             then nstring_quote (a::[])
                             else if b5
                                  then nstring_quote (a::[])
                                  else if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('t'::[]))
                   else nstring_quote (a::[])
    else if b0
         then if b1
              then nstring_quote (a::[])
              else if b2
                   then if b3
                        then nstring_quote (a::[])
                        else if b4
                             then nstring_quote (a::[])
                             else if b5
                                  then nstring_quote (a::[])
                                  else if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('n'::[]))
                   else if b3
                        then nstring_quote (a::[])
                        else if b4
                             then if b5
                                  then nstring_quote (a::[])
                                  else if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('"'::[]))
                             else nstring_quote (a::[])
         else if b1
              then if b2
                   then if b3
                        then if b4
                             then nstring_quote (a::[])
                             else if b5
                                  then if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('\\'::[]))
                                  else nstring_quote (a::[])
                        else nstring_quote (a::[])
                   else nstring_quote (a::[])
              else if b2
                   then if b3
                        then nstring_quote (a::[])
                        else if b4
                             then nstring_quote (a::[])
                             else if b5
                                  then nstring_quote (a::[])
                                  else if b6
                                       then nstring_quote (a::[])
                                       else nstring_quote ('\\'::('b'::[]))
                   else nstring_quote (a::[]))
    a

(** val js_quote_string : char list -> nstring **)

let js_quote_string s =
  nstring_flat_map js_quote_char (nstring_quote s)

(** val js_quote_number : number -> nstring **)

let js_quote_number n =
  if float_eq n Float.infinity
  then nstring_quote
         ('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[]))))))))
  else if float_eq n Float.neg_infinity
       then nstring_quote
              ('-'::('I'::('n'::('f'::('i'::('n'::('i'::('t'::('y'::[])))))))))
       else if float_eq n Float.nan
            then nstring_quote ('N'::('a'::('N'::[])))
            else nstring_quote
                   ((fun x -> Util.char_list_of_string (Util.qcert_string_of_float x))
                     n)

(** val nstring_of_literal : literal -> nstring **)

let nstring_of_literal = function
| Coq_literal_null -> nstring_quote ('n'::('u'::('l'::('l'::[]))))
| Coq_literal_bool b ->
  if b
  then nstring_quote ('t'::('r'::('u'::('e'::[]))))
  else nstring_quote ('f'::('a'::('l'::('s'::('e'::[])))))
| Coq_literal_number n -> js_quote_number n
| Coq_literal_string s ->
  nstring_append quotel (nstring_append (js_quote_string s) quotel)

(** val nstring_of_propname : propname -> nstring **)

let nstring_of_propname = function
| Coq_propname_identifier n -> nstring_quote n
| Coq_propname_string s ->
  nstring_append quotel (nstring_append (nstring_quote s) quotel)
| Coq_propname_number n ->
  nstring_quote
    ((fun x -> Util.char_list_of_string (Util.qcert_string_of_float x)) n)

(** val nstring_of_expr : expr -> int -> nstring **)

let rec nstring_of_expr e i =
  match e with
  | Coq_expr_this -> nstring_quote ('t'::('h'::('i'::('s'::[]))))
  | Coq_expr_identifier x -> nstring_quote x
  | Coq_expr_literal c -> nstring_of_literal c
  | Coq_expr_object o ->
    let props =
      map (fun prop ->
        let (name, body) = prop in
        nstring_append eol
          (nstring_append (indent (add i (Pervasives.succ 0)))
            (match body with
             | Coq_propbody_val e0 ->
               nstring_append quotel
                 (nstring_append (nstring_of_propname name)
                   (nstring_append quotel
                     (nstring_append (nstring_quote (':'::(' '::[])))
                       (nstring_append (nstring_quote ('('::[]))
                         (nstring_append
                           (nstring_of_expr e0 (add i (Pervasives.succ 0)))
                           (nstring_quote (')'::[])))))))
             | Coq_propbody_get funcbody0 ->
               nstring_append (nstring_quote ('g'::('e'::('t'::(' '::[])))))
                 (nstring_append quotel
                   (nstring_append (nstring_of_propname name)
                     (nstring_append quotel
                       (nstring_append
                         (nstring_quote ('('::(')'::(' '::('{'::[])))))
                         (nstring_append
                           (nstring_of_funcbody funcbody0
                             (add i (Pervasives.succ 0)))
                           (nstring_quote ('}'::[])))))))
             | Coq_propbody_set (args, funcbody0) ->
               nstring_append (nstring_quote ('s'::('e'::('t'::(' '::[])))))
                 (nstring_append quotel
                   (nstring_append (nstring_of_propname name)
                     (nstring_append quotel
                       (nstring_append (nstring_quote ('('::[]))
                         (nstring_append (comma_list_string args)
                           (nstring_append
                             (nstring_quote (')'::(' '::('{'::[]))))
                             (nstring_append
                               (nstring_of_funcbody funcbody0
                                 (add i (Pervasives.succ 0)))
                               (nstring_quote ('}'::[])))))))))))) o
    in
    nstring_append (nstring_quote ('{'::[]))
      (nstring_append (comma_list props)
        (nstring_append eol
          (nstring_append (indent i) (nstring_quote ('}'::[])))))
  | Coq_expr_array a ->
    let l =
      map (fun eopt ->
        match eopt with
        | Some e0 -> nstring_of_expr e0 (add i (Pervasives.succ 0))
        | None -> nstring_quote ('n'::('u'::('l'::('l'::[]))))) a
    in
    nstring_append (nstring_quote ('['::(' '::[])))
      (nstring_append (comma_list l) (nstring_quote (' '::(']'::[]))))
  | Coq_expr_function (fopt, args, body) ->
    let name =
      match fopt with
      | Some f -> nstring_quote f
      | None -> nstring_quote []
    in
    nstring_append
      (nstring_quote
        ('('::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[])))))))))))
      (nstring_append name
        (nstring_append (nstring_quote ('('::[]))
          (nstring_append (comma_list_string args)
            (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
              (nstring_append eol
                (nstring_append (indent (add i (Pervasives.succ 0)))
                  (nstring_append
                    (nstring_of_funcbody body (add i (Pervasives.succ 0)))
                    (nstring_append eol
                      (nstring_append (indent i)
                        (nstring_quote ('}'::(')'::[]))))))))))))
  | Coq_expr_access (e1, e2) ->
    nstring_append (nstring_of_expr e1 i)
      (nstring_append (nstring_quote ('['::[]))
        (nstring_append (nstring_of_expr e2 (add i (Pervasives.succ 0)))
          (nstring_quote (']'::[]))))
  | Coq_expr_member (e0, s) ->
    nstring_append (nstring_of_expr e0 i)
      (nstring_append (nstring_quote ('['::[]))
        (nstring_append quotel
          (nstring_append (nstring_quote s)
            (nstring_append quotel (nstring_quote (']'::[]))))))
  | Coq_expr_new (e0, args) ->
    let args0 =
      map (fun e1 -> nstring_of_expr e1 (add i (Pervasives.succ 0))) args
    in
    nstring_append (nstring_quote ('n'::('e'::('w'::(' '::[])))))
      (nstring_append (nstring_of_expr e0 i)
        (nstring_append (nstring_quote ('('::[]))
          (nstring_append (comma_list args0) (nstring_quote (')'::[])))))
  | Coq_expr_call (f, args) ->
    let args0 =
      map (fun e0 -> nstring_of_expr e0 (add i (Pervasives.succ 0))) args
    in
    nstring_append (nstring_of_expr f i)
      (nstring_append (nstring_quote ('('::[]))
        (nstring_append (comma_list args0) (nstring_quote (')'::[]))))
  | Coq_expr_unary_op (op, e0) ->
    let e1 = nstring_of_expr e0 (add i (Pervasives.succ 0)) in
    (match op with
     | Coq_unary_op_delete ->
       nstring_append
         (nstring_quote
           ('('::('d'::('e'::('l'::('e'::('t'::('e'::(' '::[])))))))))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_void ->
       nstring_append
         (nstring_quote ('('::('v'::('o'::('i'::('d'::(' '::[])))))))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_typeof ->
       nstring_append
         (nstring_quote
           ('('::('t'::('y'::('p'::('e'::('o'::('f'::(' '::[])))))))))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_post_incr ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e1 (nstring_quote ('+'::('+'::(')'::[])))))
     | Coq_unary_op_post_decr ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e1 (nstring_quote ('-'::('-'::(')'::[])))))
     | Coq_unary_op_pre_incr ->
       nstring_append (nstring_quote ('('::('+'::('+'::[]))))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_pre_decr ->
       nstring_append (nstring_quote ('('::('-'::('-'::[]))))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_add ->
       nstring_append (nstring_quote ('('::('+'::[])))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_neg ->
       nstring_append (nstring_quote ('('::('-'::[])))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_bitwise_not ->
       nstring_append (nstring_quote ('('::('~'::[])))
         (nstring_append e1 (nstring_quote (')'::[])))
     | Coq_unary_op_not ->
       nstring_append (nstring_quote ('('::('!'::[])))
         (nstring_append e1 (nstring_quote (')'::[]))))
  | Coq_expr_binary_op (e1, op, e2) ->
    let e3 = nstring_of_expr e1 (add i (Pervasives.succ 0)) in
    let e4 = nstring_of_expr e2 (add i (Pervasives.succ 0)) in
    (match op with
     | Coq_binary_op_mult ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('*'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_div ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('/'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_mod ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('%'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_add ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('+'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_sub ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('-'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_left_shift ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('<'::('<'::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_right_shift ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('>'::('>'::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_unsigned_right_shift ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append
             (nstring_quote (' '::('>'::('>'::('>'::(' '::[]))))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_lt ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('<'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_gt ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('>'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_le ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('<'::('='::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_ge ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('>'::('='::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_instanceof ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append
             (nstring_quote
               (' '::('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::('o'::('f'::(' '::[])))))))))))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_in ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('i'::('n'::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_equal ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('='::('='::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_disequal ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('!'::('='::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_strict_equal ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append
             (nstring_quote (' '::('='::('='::('='::(' '::[]))))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_strict_disequal ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append
             (nstring_quote (' '::('!'::('='::('='::(' '::[]))))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_bitwise_and ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('&'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_bitwise_or ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('|'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_bitwise_xor ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('^'::(' '::[]))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_and ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('&'::('&'::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_or ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (' '::('|'::('|'::(' '::[])))))
             (nstring_append e4 (nstring_quote (')'::[])))))
     | Coq_binary_op_coma ->
       nstring_append (nstring_quote ('('::[]))
         (nstring_append e3
           (nstring_append (nstring_quote (','::(' '::[])))
             (nstring_append e4 (nstring_quote (')'::[]))))))
  | Coq_expr_conditional (e1, e2, e3) ->
    let e4 = nstring_of_expr e1 (add i (Pervasives.succ 0)) in
    let e5 = nstring_of_expr e2 (add i (Pervasives.succ 0)) in
    let e6 = nstring_of_expr e3 (add i (Pervasives.succ 0)) in
    nstring_append (nstring_quote ('('::[]))
      (nstring_append e4
        (nstring_append (nstring_quote (' '::('?'::(' '::[]))))
          (nstring_append e5
            (nstring_append (nstring_quote (' '::(':'::(' '::[]))))
              (nstring_append e6 (nstring_quote (')'::[])))))))
  | Coq_expr_assign (e1, o, e2) ->
    (match o with
     | Some _ ->
       nstring_quote
         ('X'::('X'::('X'::(' '::('T'::('O'::('D'::('O'::(' '::('X'::('X'::('X'::[]))))))))))))
     | None ->
       let e3 = nstring_of_expr e1 (add i (Pervasives.succ 0)) in
       let e4 = nstring_of_expr e2 (add i (Pervasives.succ 0)) in
       nstring_append e3
         (nstring_append (nstring_quote (' '::('='::(' '::[])))) e4))

(** val nstring_of_stat : stat -> int -> nstring **)

and nstring_of_stat s i =
  nstring_append (indent i)
    (match s with
     | Coq_stat_expr e ->
       nstring_append (nstring_of_expr e i) (nstring_quote (';'::[]))
     | Coq_stat_label (lbl, s0) ->
       nstring_append (nstring_quote lbl)
         (nstring_append (nstring_quote (':'::[])) (nstring_of_stat s0 i))
     | Coq_stat_block l ->
       let seq =
         map (fun s0 -> nstring_of_stat s0 (add i (Pervasives.succ 0))) l
       in
       nstring_append (nstring_quote ('{'::[]))
         (nstring_append eol
           (nstring_append
             (nstring_concat (nstring_append (nstring_quote (';'::[])) eol)
               seq)
             (nstring_append eol
               (nstring_append (indent i) (nstring_quote ('}'::[]))))))
     | Coq_stat_var_decl l ->
       let decls =
         map (fun x_e_opt ->
           let (x, e_opt) = x_e_opt in
           nstring_append (nstring_quote ('v'::('a'::('r'::(' '::[])))))
             (nstring_append (nstring_quote x)
               (match e_opt with
                | Some e ->
                  nstring_append (nstring_quote (' '::('='::(' '::[]))))
                    (nstring_of_expr e (add i (Pervasives.succ 0)))
                | None -> nstring_quote []))) l
       in
       nstring_concat (nstring_append (nstring_quote (';'::[])) eol) decls
     | Coq_stat_let_decl l ->
       let decls =
         map (fun x_e_opt ->
           let (x, e_opt) = x_e_opt in
           nstring_append (nstring_quote ('l'::('e'::('t'::(' '::[])))))
             (nstring_append (nstring_quote x)
               (match e_opt with
                | Some e ->
                  nstring_append (nstring_quote (' '::('='::(' '::[]))))
                    (nstring_of_expr e (add i (Pervasives.succ 0)))
                | None -> nstring_quote []))) l
       in
       nstring_concat (nstring_append (nstring_quote (';'::[])) eol) decls
     | Coq_stat_if (e, s1, s2_opt) ->
       nstring_append (nstring_quote ('i'::('f'::(' '::('('::[])))))
         (nstring_append (nstring_of_expr e (add i (Pervasives.succ 0)))
           (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
             (nstring_append eol
               (nstring_append
                 (nstring_of_stat s1 (add i (Pervasives.succ 0)))
                 (nstring_append eol
                   (nstring_append (indent i)
                     (nstring_append
                       (nstring_quote
                         ('}'::(' '::('e'::('l'::('s'::('e'::(' '::('{'::[])))))))))
                       (nstring_append eol
                         (nstring_append
                           (match s2_opt with
                            | Some s2 ->
                              nstring_append
                                (nstring_of_stat s2
                                  (add i (Pervasives.succ 0))) eol
                            | None -> nstring_quote [])
                           (nstring_append (indent i)
                             (nstring_quote ('}'::[]))))))))))))
     | Coq_stat_return o ->
       (match o with
        | Some e ->
          nstring_append
            (nstring_quote
              ('r'::('e'::('t'::('u'::('r'::('n'::(' '::[]))))))))
            (nstring_append (nstring_of_expr e (add i (Pervasives.succ 0)))
              (nstring_quote (';'::[])))
        | None ->
          nstring_quote
            ('r'::('e'::('t'::('u'::('r'::('n'::(' '::(';'::[])))))))))
     | Coq_stat_for_var (_, vars, e2_opt, e3_opt, s0) ->
       let decls =
         map (fun decl ->
           let (x, e1_opt) = decl in
           nstring_append (nstring_quote x)
             (match e1_opt with
              | Some e1 ->
                nstring_append (nstring_quote (' '::('='::(' '::[]))))
                  (nstring_of_expr e1 (add i (Pervasives.succ 0)))
              | None -> nstring_quote [])) vars
       in
       nstring_append (nstring_quote ('f'::('o'::('r'::(' '::('('::[]))))))
         (nstring_append (nstring_quote ('v'::('a'::('r'::(' '::[])))))
           (nstring_append (comma_list decls)
             (nstring_append (nstring_quote (';'::(' '::[])))
               (nstring_append
                 (match e2_opt with
                  | Some e2 -> nstring_of_expr e2 (add i (Pervasives.succ 0))
                  | None -> nstring_quote [])
                 (nstring_append (nstring_quote (';'::(' '::[])))
                   (nstring_append
                     (match e3_opt with
                      | Some e3 ->
                        nstring_of_expr e3 (add i (Pervasives.succ 0))
                      | None -> nstring_quote [])
                     (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                       (nstring_append eol
                         (nstring_append
                           (nstring_of_stat s0 (add i (Pervasives.succ 0)))
                           (nstring_append eol
                             (nstring_append (indent i)
                               (nstring_append (nstring_quote ('}'::[])) eol))))))))))))
     | Coq_stat_for_let (_, vars, e2_opt, e3_opt, s0) ->
       let decls =
         map (fun decl ->
           let (x, e1_opt) = decl in
           nstring_append (nstring_quote x)
             (match e1_opt with
              | Some e1 ->
                nstring_append (nstring_quote (' '::('='::(' '::[]))))
                  (nstring_of_expr e1 (add i (Pervasives.succ 0)))
              | None -> nstring_quote [])) vars
       in
       nstring_append (nstring_quote ('f'::('o'::('r'::(' '::('('::[]))))))
         (nstring_append (nstring_quote ('l'::('e'::('t'::(' '::[])))))
           (nstring_append (comma_list decls)
             (nstring_append (nstring_quote (';'::(' '::[])))
               (nstring_append
                 (match e2_opt with
                  | Some e2 -> nstring_of_expr e2 (add i (Pervasives.succ 0))
                  | None -> nstring_quote [])
                 (nstring_append (nstring_quote (';'::(' '::[])))
                   (nstring_append
                     (match e3_opt with
                      | Some e3 ->
                        nstring_of_expr e3 (add i (Pervasives.succ 0))
                      | None -> nstring_quote [])
                     (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                       (nstring_append eol
                         (nstring_append
                           (nstring_of_stat s0 (add i (Pervasives.succ 0)))
                           (nstring_append eol
                             (nstring_append (indent i)
                               (nstring_append (nstring_quote ('}'::[])) eol))))))))))))
     | Coq_stat_for_in_var (_, x, e1_opt, e2, s0) ->
       nstring_append
         (nstring_quote
           ('f'::('o'::('r'::(' '::('('::('v'::('a'::('r'::(' '::[]))))))))))
         (nstring_append (nstring_quote x)
           (nstring_append
             (match e1_opt with
              | Some e ->
                nstring_append (nstring_quote (' '::('='::(' '::[]))))
                  (nstring_of_expr e (add i (Pervasives.succ 0)))
              | None -> nstring_quote [])
             (nstring_append (nstring_quote (' '::('i'::('n'::(' '::[])))))
               (nstring_append
                 (nstring_of_expr e2 (add i (Pervasives.succ 0)))
                 (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                   (nstring_append eol
                     (nstring_append
                       (nstring_of_stat s0 (add i (Pervasives.succ 0)))
                       (nstring_append eol
                         (nstring_append (indent i)
                           (nstring_append (nstring_quote ('}'::[])) eol))))))))))
     | Coq_stat_for_in_let (_, x, e1_opt, e2, s0) ->
       nstring_append
         (nstring_quote
           ('f'::('o'::('r'::(' '::('('::('l'::('e'::('t'::(' '::[]))))))))))
         (nstring_append (nstring_quote x)
           (nstring_append
             (match e1_opt with
              | Some e ->
                nstring_append (nstring_quote (' '::('='::(' '::[]))))
                  (nstring_of_expr e (add i (Pervasives.succ 0)))
              | None -> nstring_quote [])
             (nstring_append (nstring_quote (' '::('i'::('n'::(' '::[])))))
               (nstring_append
                 (nstring_of_expr e2 (add i (Pervasives.succ 0)))
                 (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                   (nstring_append eol
                     (nstring_append
                       (nstring_of_stat s0 (add i (Pervasives.succ 0)))
                       (nstring_append eol
                         (nstring_append (indent i)
                           (nstring_append (nstring_quote ('}'::[])) eol))))))))))
     | _ ->
       nstring_quote
         ('X'::('X'::('X'::(' '::('T'::('O'::('D'::('O'::(' '::('X'::('X'::('X'::[])))))))))))))

(** val nstring_of_element : element -> int -> nstring **)

and nstring_of_element e i =
  match e with
  | Coq_element_stat s -> nstring_of_stat s i
  | Coq_element_func_decl (f, params, body) ->
    nstring_append eol
      (nstring_append (indent i)
        (nstring_append
          (nstring_quote
            ('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::[]))))))))))
          (nstring_append (nstring_quote f)
            (nstring_append (nstring_quote ('('::[]))
              (nstring_append (comma_list_string params)
                (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                  (nstring_append eol
                    (nstring_append
                      (nstring_of_funcbody body (add i (Pervasives.succ 0)))
                      (nstring_append eol
                        (nstring_append (indent i) (nstring_quote ('}'::[]))))))))))))

(** val nstring_of_prog : prog -> int -> nstring **)

and nstring_of_prog p i =
  let Coq_prog_intro (_, elems) = p in
  let elems' = map (fun e -> nstring_of_element e i) elems in
  nstring_concat eol elems'

(** val nstring_of_funcbody : funcbody -> int -> nstring **)

and nstring_of_funcbody body i =
  let Coq_funcbody_intro (p, _) = body in nstring_of_prog p i

(** val nstring_of_method : funcdecl -> int -> nstring **)

let nstring_of_method f i =
  nstring_append eol
    (nstring_append (indent i)
      (nstring_append
        (nstring_quote ('s'::('t'::('a'::('t'::('i'::('c'::(' '::[]))))))))
        (nstring_append (nstring_quote f.funcdecl_name)
          (nstring_append (nstring_quote ('('::[]))
            (nstring_append (comma_list_string f.funcdecl_parameters)
              (nstring_append (nstring_quote (')'::(' '::('{'::[]))))
                (nstring_append eol
                  (nstring_append
                    (nstring_of_funcbody f.funcdecl_body
                      (add i (Pervasives.succ 0)))
                    (nstring_append eol
                      (nstring_append (indent i) (nstring_quote ('}'::[]))))))))))))

(** val nstring_of_decl : topdecl -> nstring **)

let nstring_of_decl = function
| Coq_strictmode ->
  nstring_append eol
    (nstring_quote
      ('\''::('u'::('s'::('e'::(' '::('s'::('t'::('r'::('i'::('c'::('t'::('\''::(';'::[]))))))))))))))
| Coq_comment c ->
  nstring_append eol
    (nstring_append (nstring_quote ('/'::('*'::[])))
      (nstring_append (nstring_quote c) (nstring_quote ('*'::('/'::[])))))
| Coq_elementdecl fd -> nstring_of_element fd 0
| Coq_classdecl (cn, cd) ->
  nstring_append eol
    (nstring_append
      (nstring_quote ('c'::('l'::('a'::('s'::('s'::(' '::[])))))))
      (nstring_append (nstring_quote cn)
        (nstring_append (nstring_quote ('{'::[]))
          (nstring_append
            (fold_left (fun acc q ->
              nstring_append acc (nstring_of_method q (Pervasives.succ 0)))
              cd (nstring_quote []))
            (nstring_append eol (nstring_quote ('}'::[])))))))
| Coq_constdecl (x, e) ->
  nstring_append eol
    (nstring_append
      (nstring_quote ('c'::('o'::('n'::('s'::('t'::(' '::[])))))))
      (nstring_append (nstring_quote x)
        (nstring_append (nstring_quote ('='::[])) (nstring_of_expr e 0))))

(** val js_ast_to_js_top : js_ast -> javascript **)

let js_ast_to_js_top ja =
  fold_left (fun acc f -> nstring_append acc (nstring_of_decl f)) ja
    (nstring_quote [])
