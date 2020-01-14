open Java
open NativeString

type uri_unary_op =
| Coq_uop_uri_encode
| Coq_uop_uri_decode

(** val uri_unary_op_tostring : uri_unary_op -> char list **)

let uri_unary_op_tostring = function
| Coq_uop_uri_encode ->
  'u'::('r'::('i'::('E'::('n'::('c'::('o'::('d'::('e'::[]))))))))
| Coq_uop_uri_decode ->
  'u'::('r'::('i'::('D'::('e'::('c'::('o'::('d'::('e'::[]))))))))

(** val cname : nstring **)

let cname =
  nstring_quote
    ('U'::('r'::('i'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[]))))))))))))

(** val uri_to_java_unary_op :
    int -> nstring -> nstring -> uri_unary_op -> java_json -> java_json **)

let uri_to_java_unary_op _ _ _ fu d =
  match fu with
  | Coq_uop_uri_encode ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('u'::('r'::('i'::('E'::('n'::('c'::('o'::('d'::('e'::[])))))))))) d
  | Coq_uop_uri_decode ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('u'::('r'::('i'::('D'::('e'::('c'::('o'::('d'::('e'::[])))))))))) d

type ejson_uri_runtime_op =
| EJsonRuntimeUriEncode
| EJsonRuntimeUriDecode

(** val ejson_uri_runtime_op_tostring : ejson_uri_runtime_op -> char list **)

let ejson_uri_runtime_op_tostring = function
| EJsonRuntimeUriEncode ->
  'u'::('r'::('i'::('E'::('n'::('c'::('o'::('d'::('e'::[]))))))))
| EJsonRuntimeUriDecode ->
  'u'::('r'::('i'::('D'::('e'::('c'::('o'::('d'::('e'::[]))))))))

(** val ejson_uri_runtime_op_fromstring :
    char list -> ejson_uri_runtime_op option **)

let ejson_uri_runtime_op_fromstring = function
| [] -> None
| a::s ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s with
                                             | [] -> None
                                             | a0::s0 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then None
                                                 else if b8
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
                                                                    (match s0 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s1 ->
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
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s2 ->
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
                                                                    then 
                                                                    if b26
                                                                    then None
                                                                    else 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then None
                                                                    else 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a3::s3 ->
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
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then None
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    None
                                                                    | a4::s4 ->
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
                                                                    then None
                                                                    else 
                                                                    if b42
                                                                    then None
                                                                    else 
                                                                    if b43
                                                                    then None
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then None
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    None
                                                                    | a5::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
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
                                                                    (match s5 with
                                                                    | [] ->
                                                                    None
                                                                    | a6::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then None
                                                                    else 
                                                                    if b56
                                                                    then None
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then None
                                                                    else 
                                                                    if b59
                                                                    then None
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then None
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    None
                                                                    | a7::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then None
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeUriEncode
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a7)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a6)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a5)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a4)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a3)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then None
                                                                    else 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then None
                                                                    else 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a3::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then None
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then None
                                                                    else 
                                                                    if b35
                                                                    then None
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    None
                                                                    | a4::s4 ->
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
                                                                    then None
                                                                    else 
                                                                    if b42
                                                                    then None
                                                                    else 
                                                                    if b43
                                                                    then None
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then None
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    None
                                                                    | a5::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
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
                                                                    (match s5 with
                                                                    | [] ->
                                                                    None
                                                                    | a6::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then None
                                                                    else 
                                                                    if b56
                                                                    then None
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then None
                                                                    else 
                                                                    if b59
                                                                    then None
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then None
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    None
                                                                    | a7::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then None
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeUriDecode
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a7)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a6)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a5)
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
                                                                    else None)
                                                                    a2)
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
              else None
    else None)
    a
