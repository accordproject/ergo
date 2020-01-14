open EquivDec
open List0
open Nat

type digit = int

(** val nat_to_digits_backwards : int -> int -> digit list **)

let rec nat_to_digits_backwards base x =
  if equiv_dec nat_eq_eqdec x 0
  then []
  else (modulo x base) :: (nat_to_digits_backwards base (div x base))

(** val nat_to_digits : int -> int -> digit list **)

let nat_to_digits base n =
  rev (nat_to_digits_backwards base n)

(** val digit_to_char : int -> digit -> char **)

let digit_to_char _ n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> '0')
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> '1')
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> '2')
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> '3')
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> '4')
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> '5')
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> '6')
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> '7')
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> '8')
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> '9')
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> 'A')
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> 'B')
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> 'C')
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> 'D')
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> 'E')
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> 'F')
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> 'G')
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> 'H')
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> 'I')
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> 'J')
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> 'K')
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> 'L')
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> 'M')
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> 'N')
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ -> 'O')
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      'P')
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        'Q')
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          'R')
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            'S')
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              'T')
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                'U')
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  'V')
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    'W')
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    'X')
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    'Y')
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    'Z')
                                                                    (fun _ ->
                                                                    '?')
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    n

(** val list_to_string : char list -> char list **)

let rec list_to_string = function
| [] -> []
| x :: xs -> x::(list_to_string xs)

(** val digits_to_string_aux : int -> digit list -> char list **)

let digits_to_string_aux base ld =
  list_to_string (map (digit_to_char base) ld)

(** val digits_to_string : int -> digit list -> char list **)

let digits_to_string base ld =
  match digits_to_string_aux base ld with
  | [] -> '0'::[]
  | a::s0 -> a::s0

(** val nat_to_string : int -> int -> char list **)

let nat_to_string base n =
  digits_to_string base (nat_to_digits base n)

(** val nat_to_string10 : int -> char list **)

let nat_to_string10 = (fun x -> Util.char_list_of_string (string_of_int x))

(** val coq_Z_to_string10 : int -> char list **)

let coq_Z_to_string10 = (fun x -> Util.char_list_of_string (string_of_int x))

(** val nat_to_string16 : int -> char list **)

let nat_to_string16 =
  nat_to_string (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))
