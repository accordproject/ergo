
(** val key_encode : char list -> char list **)

let key_encode s = match s with
| [] -> s
| a::s0 ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then s
    else if b0
         then s
         else if b1
              then if b2
                   then s
                   else if b3
                        then s
                        else if b4
                             then if b5
                                  then s
                                  else if b6 then s else '$'::('$'::s0)
                             else s
              else s)
    a

(** val key_decode : char list -> char list **)

let key_decode s = match s with
| [] -> []
| a::s0 ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then s
    else if b0
         then s
         else if b1
              then if b2
                   then s
                   else if b3
                        then s
                        else if b4
                             then if b5
                                  then s
                                  else if b6
                                       then s
                                       else (match s0 with
                                             | [] -> s
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then s
                                                 else if b8
                                                      then s
                                                      else if b9
                                                           then if b10
                                                                then s
                                                                else 
                                                                  if b11
                                                                  then s
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then s
                                                                    else 
                                                                    if b14
                                                                    then s
                                                                    else 
                                                                    '$'::s1
                                                                    else s
                                                           else s)
                                                 a0)
                             else s
              else s)
    a
