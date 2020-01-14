
(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append = (fun s1 s2 -> Util.char_list_append s1 s2)

(** val length : char list -> int **)

let rec length = function
| [] -> 0
| _::s' -> Pervasives.succ (length s')

(** val substring : int -> int -> char list -> char list **)

let rec substring n m s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun m' -> match s with
                 | [] -> s
                 | c::s' -> c::(substring 0 m' s'))
      m)
    (fun n' -> match s with
               | [] -> s
               | _::s' -> substring n' m s')
    n

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

(** val index : int -> char list -> char list -> int option **)

let rec index n s1 s2 = match s2 with
| [] ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> match s1 with
               | [] -> Some 0
               | _::_ -> None)
     (fun _ -> None)
     n)
| _::s2' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     if prefix s1 s2
     then Some 0
     else (match index 0 s1 s2' with
           | Some n0 -> Some (Pervasives.succ n0)
           | None -> None))
     (fun n' ->
     match index n' s1 s2' with
     | Some n0 -> Some (Pervasives.succ n0)
     | None -> None)
     n)
