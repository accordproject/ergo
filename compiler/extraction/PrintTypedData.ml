open Ascii
open CoqLibAdd
open Data
open Datatypes
open Lift
open List0
open Misc
open Names
open NamespaceContext
open Provenance
open QcertData
open QcertType
open RType
open Result0
open String0
open StringAdd
open TBrandModel
open ToString
open UnaryOperators
open UnaryOperatorsSem

(** val print_brand : namespace_ctxt -> char list -> char list **)

let print_brand nsctxt b =
  match get_local_part b with
  | Some local_name ->
    elift_both (fun resolved_b ->
      if string_dec resolved_b b then local_name else append ('~'::[]) b)
      (fun _ -> append ('~'::[]) b)
      (resolve_type_name dummy_provenance nsctxt (None, local_name))
  | None -> append ('~'::[]) b

(** val print_multiple_brands :
    namespace_ctxt -> char list list -> char list **)

let print_multiple_brands nsctxt bs =
  append ('<'::[])
    (append (map_concat (','::[]) (print_brand nsctxt) bs) ('>'::[]))

(** val unpack_output :
    QLib.qcert_data -> ((QLib.qcert_data * QLib.qcert_data
    list) * QLib.qcert_data) option **)

let unpack_output = function
| Coq_dleft d ->
  (match d with
   | Coq_drec l ->
     (match l with
      | [] -> None
      | p :: l0 ->
        let (s, d0) = p in
        (match s with
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
                       then if b2
                            then if b3
                                 then if b4
                                      then None
                                      else if b5
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
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then None
                                                                    else 
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
                                                                    then 
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
                                                                    then 
                                                                    if b24
                                                                    then None
                                                                    else 
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
                                                                    None
                                                                    | a3::s4 ->
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
                                                                    then None
                                                                    else 
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
                                                                    then None
                                                                    else 
                                                                    if b40
                                                                    then None
                                                                    else 
                                                                    if b41
                                                                    then 
                                                                    if b42
                                                                    then None
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then None
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    (match d0 with
                                                                    | Coq_dcoll emits ->
                                                                    (match l0 with
                                                                    | [] ->
                                                                    None
                                                                    | p0 :: l1 ->
                                                                    let (
                                                                    s6,
                                                                    response) =
                                                                    p0
                                                                    in
                                                                    (
                                                                    match s6 with
                                                                    | [] ->
                                                                    None
                                                                    | a5::s7 ->
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
                                                                    then 
                                                                    if b52
                                                                    then None
                                                                    else 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then None
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    None
                                                                    | a6::s8 ->
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
                                                                    then 
                                                                    if b58
                                                                    then 
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
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a7::s9 ->
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
                                                                    then 
                                                                    if b65
                                                                    then None
                                                                    else 
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
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s10 ->
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
                                                                    then None
                                                                    else 
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
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s11 ->
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
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s12 ->
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
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then None
                                                                    else 
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
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s13 ->
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
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s14 ->
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
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
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
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s16 ->
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
                                                                    then None
                                                                    else 
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
                                                                    (match s16 with
                                                                    | [] ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    None
                                                                    | p1 :: l2 ->
                                                                    let (
                                                                    s17, state) =
                                                                    p1
                                                                    in
                                                                    (
                                                                    match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then None
                                                                    else 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then None
                                                                    else 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s21 ->
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
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    (match l2 with
                                                                    | [] ->
                                                                    Some
                                                                    ((response,
                                                                    emits),
                                                                    state)
                                                                    | _ :: _ ->
                                                                    None)
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15))
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
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
                                                                    a5))
                                                                    | _ ->
                                                                    None)
                                                                    | _::_ ->
                                                                    None)
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
                                                                    else None
                                                                    else None
                                                               else None
                                                          else None)
                                                          a0)
                                           else None
                                 else None
                            else None
                       else None
                  else None
             else None)
             a))
   | _ -> None)
| _ -> None

(** val fmt_nl : char list **)

let fmt_nl =
  (ascii_of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))::[]

(** val string_of_enum : namespace_ctxt -> QLib.qcert_data -> char list **)

let rec string_of_enum nsctxt = function
| Coq_dleft d0 ->
  (match d0 with
   | Coq_dstring x -> x
   | _ ->
     '?'::('?'::('?'::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('n'::('u'::('m'::('?'::('?'::('?'::[]))))))))))))))))))))
| Coq_dright d' -> string_of_enum nsctxt d'
| _ ->
  '?'::('?'::('?'::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('e'::('n'::('u'::('m'::('?'::('?'::('?'::[])))))))))))))))))))

(** val string_of_data : namespace_ctxt -> QLib.qcert_data -> char list **)

let rec string_of_data nsctxt d =
  let string_of_rec = fun rec0 ->
    append ('{'::[])
      (append
        (concat (','::(' '::[]))
          (map (fun item ->
            append (fst item)
              (append (':'::(' '::[])) (string_of_data nsctxt (snd item))))
            rec0)) ('}'::[]))
  in
  (match d with
   | Coq_dunit -> 'u'::('n'::('i'::('t'::[])))
   | Coq_dnat z -> toString coq_ToString_Z z
   | Coq_dfloat f ->
     append ('"'::[]) (append (toString coq_ToString_float f) ('"'::[]))
   | Coq_dbool b ->
     if b
     then 't'::('r'::('u'::('e'::[])))
     else 'f'::('a'::('l'::('s'::('e'::[]))))
   | Coq_dstring s ->
     toString
       (coq_ToString_data enhanced_foreign_data enhanced_foreign_operators)
       (Coq_dstring s)
   | Coq_dcoll arr ->
     append ('['::[])
       (append (concat (','::(' '::[])) (map (string_of_data nsctxt) arr))
         (']'::[]))
   | Coq_drec r -> string_of_rec r
   | Coq_dleft s ->
     append ('s'::('o'::('m'::('e'::('('::[])))))
       (append (string_of_data nsctxt s) (')'::[]))
   | Coq_dright _ -> 'n'::('o'::('n'::('e'::[])))
   | Coq_dbrand (b0, d') ->
     (match b0 with
      | [] ->
        '?'::('?'::('?'::('m'::('o'::('r'::('e'::(' '::('t'::('h'::('a'::('n'::(' '::('o'::('n'::('e'::(' '::('b'::('r'::('a'::('n'::('d'::('?'::('?'::('?'::[]))))))))))))))))))))))))
      | b :: l ->
        (match l with
         | [] ->
           (match d' with
            | Coq_dleft x -> string_of_enum nsctxt (Coq_dleft x)
            | Coq_dright x -> string_of_enum nsctxt (Coq_dright x)
            | _ -> append (print_brand nsctxt b) (string_of_data nsctxt d'))
         | _ :: _ ->
           '?'::('?'::('?'::('m'::('o'::('r'::('e'::(' '::('t'::('h'::('a'::('n'::(' '::('o'::('n'::('e'::(' '::('b'::('r'::('a'::('n'::('d'::('?'::('?'::('?'::[]))))))))))))))))))))))))))
   | Coq_dforeign f0 ->
     (match Obj.magic f0 with
      | Coq_enhanceddateTimeformat f ->
        append
          ('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::('('::('"'::[]))))))))))))))))
          (append
            ((fun x -> Util.char_list_of_string (Date_time_component.format_to_string x))
              f) ('"'::(')'::[])))
      | Coq_enhanceddateTime dt ->
        append
          ('d'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('('::('"'::[]))))))))))
          (append
            ((fun x f -> Util.char_list_of_string (Date_time_component.to_string_format x f))
              dt
              ((fun x -> Date_time_component.format_from_string (Util.string_of_char_list x))
                ('M'::('M'::('/'::('D'::('D'::('/'::('Y'::('Y'::('Y'::('Y'::[]))))))))))))
            ('"'::(')'::[])))
      | Coq_enhanceddateTimeduration dti ->
        append
          ('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('('::[])))))))))
          (append
            ((fun x -> Util.char_list_of_string (Date_time_component.duration_to_string x))
              dti) (')'::[]))
      | Coq_enhanceddateTimeperiod dti ->
        append ('p'::('e'::('r'::('i'::('o'::('d'::('('::[])))))))
          (append
            ((fun x -> Util.char_list_of_string (Date_time_component.period_to_string x))
              dti) (')'::[]))))

(** val rtype_to_string : namespace_ctxt -> rtype_UU2080_ -> char list **)

let rec rtype_to_string nsctxt = function
| Bottom_UU2080_ -> 'N'::('o'::('t'::('h'::('i'::('n'::('g'::[]))))))
| Top_UU2080_ -> 'A'::('n'::('y'::[]))
| Unit_UU2080_ -> 'U'::('n'::('i'::('t'::[])))
| Nat_UU2080_ -> 'I'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))
| Float_UU2080_ -> 'D'::('o'::('u'::('b'::('l'::('e'::[])))))
| Bool_UU2080_ -> 'B'::('o'::('o'::('l'::('e'::('a'::('n'::[]))))))
| String_UU2080_ -> 'S'::('t'::('r'::('i'::('n'::('g'::[])))))
| Coll_UU2080_ r' -> append (rtype_to_string nsctxt r') ('['::(']'::[]))
| Rec_UU2080_ (k, srl) ->
  let recend = match k with
               | Open -> ' '::('.'::('.'::[]))
               | Closed -> [] in
  append ('{'::[])
    (append
      (concat (','::(' '::[]))
        (map (fun sr ->
          append (fst sr)
            (append (':'::(' '::[])) (rtype_to_string nsctxt (snd sr)))) srl))
      (append recend ('}'::[])))
| Either_UU2080_ (tl, _) -> append (rtype_to_string nsctxt tl) ('?'::[])
| Arrow_UU2080_ (tin, tout) ->
  append (rtype_to_string nsctxt tin)
    (append (' '::('-'::('>'::(' '::[])))) (rtype_to_string nsctxt tout))
| Brand_UU2080_ bs ->
  (match bs with
   | [] -> print_multiple_brands nsctxt bs
   | b :: l ->
     (match l with
      | [] -> print_brand nsctxt b
      | _ :: _ -> print_multiple_brands nsctxt bs))
| Foreign_UU2080_ ft ->
  (match Obj.magic ft with
   | Coq_enhancedDateTimeFormat ->
     'D'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))
   | Coq_enhancedDateTime ->
     'D'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::[])))))))
   | Coq_enhancedDateTimeDuration ->
     'I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))
   | Coq_enhancedDateTimePeriod ->
     'I'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::('P'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))
   | _ ->
     '('::('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('o'::('r'::('e'::('i'::('g'::('n'::(' '::('t'::('y'::('p'::('e'::(')'::[]))))))))))))))))))))))

(** val qcert_type_to_string :
    brand_model -> namespace_ctxt -> QLib.qcert_type -> char list **)

let qcert_type_to_string br nsctxt t =
  rtype_to_string nsctxt
    (QLib.QcertType.qcert_type_unpack br.brand_model_relation t)

(** val string_of_result_type :
    brand_model -> namespace_ctxt -> QLib.qcert_type option -> char list **)

let string_of_result_type br nsctxt = function
| Some typ ->
  append (' '::(':'::(' '::[]))) (qcert_type_to_string br nsctxt typ)
| None -> []

(** val unpack_error :
    brand_model -> namespace_ctxt -> char list -> QLib.qcert_type -> eerror **)

let unpack_error br nsctxt kind out =
  ESystemError (dummy_provenance,
    (append
      ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('u'::('n'::('p'::('a'::('c'::('k'::(' '::('t'::('y'::('p'::('e'::(':'::(' '::[]))))))))))))))))))))
      (append (string_of_result_type br nsctxt (Some out))
        (append
          (' '::('('::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::[])))))))))))
          (append kind (')'::[]))))))

(** val unpack_failure_type :
    brand_model -> namespace_ctxt -> QLib.qcert_type -> QLib.qcert_type
    eresult **)

let unpack_failure_type br nsctxt out =
  let osuccess = QLib.QcertType.unteither br out in
  eresult_of_option (lift snd osuccess)
    (unpack_error br nsctxt ('e'::('i'::('t'::('h'::('e'::('r'::[])))))) out)
    []

(** val unpack_success_type :
    brand_model -> namespace_ctxt -> QLib.qcert_type -> ewarning list ->
    ((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) eresult **)

let unpack_success_type br nsctxt out warnings =
  let osuccess = QLib.QcertType.unteither br out in
  let success =
    eresult_of_option (lift fst osuccess)
      (unpack_error br nsctxt ('e'::('i'::('t'::('h'::('e'::('r'::[]))))))
        out) []
  in
  let response =
    elift fst
      (eolift (fun success0 ->
        eresult_of_option
          (QLib.QcertType.qcert_type_infer_unary_op br (OpDot this_response)
            success0) (unpack_error br nsctxt this_response out) []) success)
  in
  let emit =
    elift fst
      (eolift (fun success0 ->
        eresult_of_option
          (QLib.QcertType.qcert_type_infer_unary_op br (OpDot this_emit)
            success0) (unpack_error br nsctxt this_emit out) []) success)
  in
  let state =
    elift fst
      (eolift (fun success0 ->
        eresult_of_option
          (QLib.QcertType.qcert_type_infer_unary_op br (OpDot this_state)
            success0) (unpack_error br nsctxt this_state out) warnings)
        success)
  in
  elift3 (fun r e s -> ((r, e), s)) response emit state

(** val unpack_output_type :
    brand_model -> namespace_ctxt -> QLib.qcert_type -> ewarning list ->
    (((QLib.qcert_type * QLib.qcert_type) * QLib.qcert_type) * QLib.qcert_type)
    eresult **)

let unpack_output_type br nsctxt out warnings =
  elift2 (fun x y -> (x, y)) (unpack_success_type br nsctxt out warnings)
    (unpack_failure_type br nsctxt out)

(** val string_of_response :
    brand_model -> namespace_ctxt -> QLib.qcert_data -> QLib.qcert_type
    option -> char list **)

let string_of_response br nsctxt response response_type =
  append
    ('R'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::('.'::(' '::[]))))))))))
    (append (string_of_data nsctxt response)
      (string_of_result_type br nsctxt response_type))

(** val string_of_emits :
    brand_model -> namespace_ctxt -> QLib.qcert_data list -> QLib.qcert_type
    option -> char list **)

let string_of_emits br nsctxt emits emit_type =
  match emits with
  | [] -> []
  | e1 :: erest ->
    append
      (fold_right (fun new0 old ->
        append old
          (append fmt_nl
            (append ('E'::('m'::('i'::('t'::('.'::(' '::[])))))) new0)))
        (append ('E'::('m'::('i'::('t'::('.'::(' '::[]))))))
          (string_of_data nsctxt e1)) (map (string_of_data nsctxt) erest))
      (append (string_of_result_type br nsctxt emit_type) fmt_nl)

(** val string_of_state :
    brand_model -> namespace_ctxt -> QLib.qcert_data option ->
    QLib.qcert_data -> QLib.qcert_type option -> char list **)

let string_of_state br nsctxt old_state new_state state_type =
  let jsonify = string_of_data nsctxt in
  (match old_state with
   | Some actual_old_state ->
     if data_eq_dec enhanced_foreign_data new_state actual_old_state
     then []
     else append fmt_nl
            (append ('S'::('t'::('a'::('t'::('e'::('.'::(' '::[])))))))
              (append (jsonify new_state)
                (string_of_result_type br nsctxt state_type)))
   | None ->
     append fmt_nl
       (append ('S'::('t'::('a'::('t'::('e'::('.'::(' '::[])))))))
         (append (jsonify new_state)
           (string_of_result_type br nsctxt state_type))))

(** val string_of_typed_data :
    brand_model -> namespace_ctxt -> QLib.qcert_data option ->
    QLib.qcert_data -> QLib.qcert_type option -> char list **)

let string_of_typed_data br nsctxt old_state data typ =
  match data with
  | Coq_dunit ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dnat _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dfloat _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dbool _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dstring _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dcoll _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_drec _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dleft _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dright msg ->
    let failure_type =
      match typ with
      | Some typ0 ->
        elift_both (fun x -> Some x) (fun _ -> None)
          (unpack_failure_type br nsctxt typ0)
      | None -> None
    in
    append ('F'::('a'::('i'::('l'::('u'::('r'::('e'::('.'::(' '::[])))))))))
      (append (string_of_data nsctxt msg)
        (string_of_result_type br nsctxt failure_type))
  | Coq_dbrand (_, _) ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)
  | Coq_dforeign _ ->
    (match unpack_output data with
     | Some p ->
       let (p0, state) = p in
       let (response, emits) = p0 in
       let (p1, state_type) =
         match typ with
         | Some typ0 ->
           elift_both (fun res ->
             let (y, s) = res in
             let (r, e) = y in (((Some r), (Some e)), (Some s))) (fun _ ->
             ((None, None), None)) (unpack_success_type br nsctxt typ0 [])
         | None -> ((None, None), None)
       in
       let (response_type, emit_type) = p1 in
       append (string_of_emits br nsctxt emits emit_type)
         (append (string_of_response br nsctxt response response_type)
           (string_of_state br nsctxt old_state state state_type))
     | None -> string_of_data nsctxt data)

(** val string_of_typed_result :
    brand_model -> namespace_ctxt -> QLib.qcert_data option ->
    (QLib.qcert_type option * QLib.qcert_data option) -> char list **)

let string_of_typed_result br nsctxt old_state = function
| (typ, o) ->
  (match o with
   | Some dat ->
     append (string_of_typed_data br nsctxt old_state dat typ) fmt_nl
   | None -> [])
