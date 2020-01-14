open Java
open NativeString

type monetary_amount_binary_op =
| Coq_bop_monetary_amount_format
| Coq_bop_monetary_code_format

(** val monetary_amount_binary_op_tostring :
    monetary_amount_binary_op -> char list **)

let monetary_amount_binary_op_tostring = function
| Coq_bop_monetary_amount_format ->
  'm'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('A'::('m'::('o'::('u'::('n'::('t'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))))
| Coq_bop_monetary_code_format ->
  'm'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('C'::('o'::('d'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))

(** val cname : nstring **)

let cname =
  nstring_quote
    ('M'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('A'::('m'::('o'::('u'::('n'::('t'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[])))))))))))))))))))))))

(** val monetary_amount_to_java_binary_op :
    int -> nstring -> nstring -> monetary_amount_binary_op -> java_json ->
    java_json -> java_json **)

let monetary_amount_to_java_binary_op _ _ _ fb d1 d2 =
  match fb with
  | Coq_bop_monetary_amount_format ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('m'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('_'::('a'::('m'::('o'::('u'::('n'::('t'::('_'::('f'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))))))))
      d1 d2
  | Coq_bop_monetary_code_format ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('m'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('_'::('c'::('o'::('d'::('e'::('_'::('f'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))))))
      d1 d2

type ejson_monetary_amount_runtime_op =
| EJsonRuntimeMonetaryAmountFormat
| EJsonRuntimeMonetaryCodeFormat

(** val ejson_monetary_amount_runtime_op_tostring :
    ejson_monetary_amount_runtime_op -> char list **)

let ejson_monetary_amount_runtime_op_tostring = function
| EJsonRuntimeMonetaryAmountFormat ->
  'm'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('A'::('m'::('o'::('u'::('n'::('t'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))))
| EJsonRuntimeMonetaryCodeFormat ->
  'm'::('o'::('n'::('e'::('t'::('a'::('r'::('y'::('C'::('o'::('d'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))

(** val ejson_monetary_amount_runtime_op_fromstring :
    char list -> ejson_monetary_amount_runtime_op option **)

let ejson_monetary_amount_runtime_op_fromstring = function
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
         then None
         else if b1
              then if b2
                   then if b3
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
                                                                    then 
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
                                                                    then None
                                                                    else 
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
                                                                    then None
                                                                    else 
                                                                    if b50
                                                                    then None
                                                                    else 
                                                                    if b51
                                                                    then 
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
                                                                    then None
                                                                    else 
                                                                    if b57
                                                                    then None
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
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
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then None
                                                                    else 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
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
                                                                    then 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
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
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then None
                                                                    else 
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
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
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
                                                                    then None
                                                                    else 
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
                                                                    then None
                                                                    else 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeMonetaryCodeFormat
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b65
                                                                    then None
                                                                    else 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
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
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
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
                                                                    then 
                                                                    if b81
                                                                    then 
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
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
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
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then 
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
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then None
                                                                    else 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then None
                                                                    else 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeMonetaryAmountFormat
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
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
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else None)
                                                                    a7)
                                                                    else None
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
                                                                    else None)
                                                                    a4)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a3)
                                                                    else None
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
                   else None
              else None
    else None)
    a
