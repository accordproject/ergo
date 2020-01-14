open Java
open NativeString

type __ = Obj.t

type math_unary_op =
| Coq_uop_math_float_of_string
| Coq_uop_math_acos
| Coq_uop_math_asin
| Coq_uop_math_atan
| Coq_uop_math_cos
| Coq_uop_math_cosh
| Coq_uop_math_sin
| Coq_uop_math_sinh
| Coq_uop_math_tan
| Coq_uop_math_tanh

(** val math_unary_op_tostring : math_unary_op -> char list **)

let math_unary_op_tostring = function
| Coq_uop_math_float_of_string ->
  'f'::('l'::('o'::('a'::('t'::('O'::('f'::('S'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))
| Coq_uop_math_acos -> 'a'::('c'::('o'::('s'::[])))
| Coq_uop_math_asin -> 'a'::('s'::('i'::('n'::[])))
| Coq_uop_math_atan -> 'a'::('t'::('a'::('n'::[])))
| Coq_uop_math_cos -> 'c'::('o'::('s'::[]))
| Coq_uop_math_cosh -> 'c'::('o'::('s'::('h'::[])))
| Coq_uop_math_sin -> 's'::('i'::('n'::[]))
| Coq_uop_math_sinh -> 's'::('i'::('n'::('h'::[])))
| Coq_uop_math_tan -> 't'::('a'::('n'::[]))
| Coq_uop_math_tanh -> 't'::('a'::('n'::('h'::[])))

(** val math_binary_op_tostring : __ -> char list **)

let math_binary_op_tostring _ =
  'a'::('t'::('a'::('n'::('2'::[]))))

(** val cname : nstring **)

let cname =
  nstring_quote
    ('M'::('a'::('t'::('h'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[])))))))))))))

(** val math_to_java_unary_op :
    int -> nstring -> nstring -> math_unary_op -> java_json -> java_json **)

let math_to_java_unary_op _ _ _ fu d =
  match fu with
  | Coq_uop_math_float_of_string ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('f'::('l'::('o'::('a'::('t'::('O'::('f'::('S'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))))
      d
  | Coq_uop_math_acos ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('a'::('c'::('o'::('s'::[]))))) d
  | Coq_uop_math_asin ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('a'::('s'::('i'::('n'::[]))))) d
  | Coq_uop_math_atan ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('a'::('t'::('a'::('n'::[]))))) d
  | Coq_uop_math_cos ->
    mk_java_unary_op0_foreign cname (nstring_quote ('c'::('o'::('s'::[])))) d
  | Coq_uop_math_cosh ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('c'::('o'::('s'::('h'::[]))))) d
  | Coq_uop_math_sin ->
    mk_java_unary_op0_foreign cname (nstring_quote ('s'::('i'::('n'::[])))) d
  | Coq_uop_math_sinh ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('s'::('i'::('n'::('h'::[]))))) d
  | Coq_uop_math_tan ->
    mk_java_unary_op0_foreign cname (nstring_quote ('t'::('a'::('n'::[])))) d
  | Coq_uop_math_tanh ->
    mk_java_unary_op0_foreign cname
      (nstring_quote ('t'::('a'::('n'::('h'::[]))))) d

(** val math_to_java_binary_op :
    int -> nstring -> nstring -> java_json -> java_json -> java_json **)

let math_to_java_binary_op _ _ _ d1 d2 =
  mk_java_binary_op0_foreign cname
    (nstring_quote ('a'::('t'::('a'::('n'::('2'::[])))))) d1 d2

type ejson_math_runtime_op =
| EJsonRuntimeFloatOfString
| EJsonRuntimeAcos
| EJsonRuntimeAsin
| EJsonRuntimeAtan
| EJsonRuntimeAtan2
| EJsonRuntimeCos
| EJsonRuntimeCosh
| EJsonRuntimeSin
| EJsonRuntimeSinh
| EJsonRuntimeTan
| EJsonRuntimeTanh

(** val ejson_math_runtime_op_tostring :
    ejson_math_runtime_op -> char list **)

let ejson_math_runtime_op_tostring = function
| EJsonRuntimeFloatOfString ->
  'f'::('l'::('o'::('a'::('t'::('O'::('f'::('S'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))
| EJsonRuntimeAcos -> 'a'::('c'::('o'::('s'::[])))
| EJsonRuntimeAsin -> 'a'::('s'::('i'::('n'::[])))
| EJsonRuntimeAtan -> 'a'::('t'::('a'::('n'::[])))
| EJsonRuntimeAtan2 -> 'a'::('t'::('a'::('n'::('2'::[]))))
| EJsonRuntimeCos -> 'c'::('o'::('s'::[]))
| EJsonRuntimeCosh -> 'c'::('o'::('s'::('h'::[])))
| EJsonRuntimeSin -> 's'::('i'::('n'::[]))
| EJsonRuntimeSinh -> 's'::('i'::('n'::('h'::[])))
| EJsonRuntimeTan -> 't'::('a'::('n'::[]))
| EJsonRuntimeTanh -> 't'::('a'::('n'::('h'::[])))

(** val ejson_math_runtime_op_fromstring :
    char list -> ejson_math_runtime_op option **)

let ejson_math_runtime_op_fromstring = function
| [] -> None
| a::s0 ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then if b1
              then None
              else if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then if b8
                                                      then None
                                                      else if b9
                                                           then None
                                                           else if b10
                                                                then 
                                                                  if b11
                                                                  then None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then None
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeSin
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then None
                                                                    else 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then None
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeSinh
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                                else None
                                                 else None)
                                                 a0)
                                  else None
                             else None
                        else if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then if b8
                                                      then if b9
                                                           then if b10
                                                                then 
                                                                  if b11
                                                                  then None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then None
                                                                    else 
                                                                    if b18
                                                                    then None
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeCos
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then None
                                                                    else 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then None
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeCosh
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                                else None
                                                           else None
                                                      else None
                                                 else None)
                                                 a0)
                                  else None
                             else None
         else if b1
              then None
              else if b2
                   then None
                   else if b3
                        then None
                        else if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then if b8
                                                      then if b9
                                                           then None
                                                           else if b10
                                                                then None
                                                                else 
                                                                  if b11
                                                                  then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then None
                                                                    else 
                                                                    if b17
                                                                    then None
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then None
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeAsin
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then None
                                                                    else 
                                                                    if b26
                                                                    then None
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeAcos
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                      else None
                                                 else if b8
                                                      then None
                                                      else if b9
                                                           then if b10
                                                                then None
                                                                else 
                                                                  if b11
                                                                  then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then None
                                                                    else 
                                                                    if b17
                                                                    then None
                                                                    else 
                                                                    if b18
                                                                    then None
                                                                    else 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then None
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeAtan
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then None
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    if b33
                                                                    then None
                                                                    else 
                                                                    if b34
                                                                    then None
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then None
                                                                    else 
                                                                    if b38
                                                                    then None
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeAtan2
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a3)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                                  else None
                                                           else None)
                                                 a0)
                                  else None
                             else None
    else if b0
         then if b1
              then if b2
                   then None
                   else if b3
                        then None
                        else if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then None
                                                 else if b8
                                                      then None
                                                      else if b9
                                                           then if b10
                                                                then 
                                                                  if b11
                                                                  then None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then None
                                                                    else 
                                                                    if b26
                                                                    then None
                                                                    else 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    None
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then None
                                                                    else 
                                                                    if b32
                                                                    then None
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then None
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then None
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    None
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then 
                                                                    if b43
                                                                    then None
                                                                    else 
                                                                    if b44
                                                                    then None
                                                                    else 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then None
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    None
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then None
                                                                    else 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then None
                                                                    else 
                                                                    if b51
                                                                    then None
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then None
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    None
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then 
                                                                    if b57
                                                                    then None
                                                                    else 
                                                                    if b58
                                                                    then None
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then None
                                                                    else 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then None
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    None
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then None
                                                                    else 
                                                                    if b64
                                                                    then None
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then None
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then None
                                                                    else 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeFloatOfString
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a7)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a6)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a5)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a4)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a3)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                                else None
                                                           else None)
                                                 a0)
                                  else None
                             else None
              else None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then if b8
                                                      then None
                                                      else if b9
                                                           then None
                                                           else if b10
                                                                then None
                                                                else 
                                                                  if b11
                                                                  then None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then None
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then None
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeTan
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then None
                                                                    else 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then None
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeTanh
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                 else None)
                                                 a0)
                                  else None
                             else None
                        else None
              else None)
    a
