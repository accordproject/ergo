open Ascii
open List0
open NativeString
open String0
open StringAdd

(** val eol_newline : char list **)

let eol_newline =
  (ascii_of_nat (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))::[]

(** val neol_newline : nstring **)

let neol_newline =
  nstring_quote eol_newline

(** val quotel_double : char list **)

let quotel_double =
  '"'::[]

(** val nquotel_double : nstring **)

let nquotel_double =
  nstring_quote quotel_double

(** val indent : int -> nstring **)

let rec indent i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> nstring_quote [])
    (fun j -> nstring_append (nstring_quote (' '::(' '::[]))) (indent j))
    i

(** val string_bracket : char list -> char list -> char list -> char list **)

let string_bracket open0 s close =
  append open0 (append s close)

(** val nstring_bracket : nstring -> nstring -> nstring -> nstring **)

let nstring_bracket open0 s close =
  nstring_append open0 (nstring_append s close)

(** val jsAllowedIdentifierInitialCharacters : char list **)

let jsAllowedIdentifierInitialCharacters =
  'A' :: ('B' :: ('C' :: ('D' :: ('E' :: ('F' :: ('G' :: ('H' :: ('I' :: ('J' :: ('K' :: ('L' :: ('M' :: ('N' :: ('O' :: ('P' :: ('Q' :: ('R' :: ('S' :: ('T' :: ('U' :: ('V' :: ('W' :: ('X' :: ('Y' :: ('Z' :: ('a' :: ('b' :: ('c' :: ('d' :: ('e' :: ('f' :: ('g' :: ('h' :: ('i' :: ('j' :: ('k' :: ('l' :: ('m' :: ('n' :: ('o' :: ('p' :: ('q' :: ('r' :: ('s' :: ('t' :: ('u' :: ('v' :: ('w' :: ('x' :: ('y' :: ('z' :: [])))))))))))))))))))))))))))))))))))))))))))))))))))

(** val jsAllowedIdentifierCharacters : char list **)

let jsAllowedIdentifierCharacters =
  'A' :: ('B' :: ('C' :: ('D' :: ('E' :: ('F' :: ('G' :: ('H' :: ('I' :: ('J' :: ('K' :: ('L' :: ('M' :: ('N' :: ('O' :: ('P' :: ('Q' :: ('R' :: ('S' :: ('T' :: ('U' :: ('V' :: ('W' :: ('X' :: ('Y' :: ('Z' :: ('a' :: ('b' :: ('c' :: ('d' :: ('e' :: ('f' :: ('g' :: ('h' :: ('i' :: ('j' :: ('k' :: ('l' :: ('m' :: ('n' :: ('o' :: ('p' :: ('q' :: ('r' :: ('s' :: ('t' :: ('u' :: ('v' :: ('w' :: ('x' :: ('y' :: ('z' :: ('0' :: ('1' :: ('2' :: ('3' :: ('4' :: ('5' :: ('6' :: ('7' :: ('8' :: ('9' :: ('_' :: ('$' :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val jsIdentifierInitialCharacterToAdd : char **)

let jsIdentifierInitialCharacterToAdd =
  'X'

(** val jsIdenitiferCharacterForReplacement : char **)

let jsIdenitiferCharacterForReplacement =
  'X'

(** val jsIdentifierFixInitial : char list -> char list **)

let jsIdentifierFixInitial ident = match ident with
| [] -> jsIdentifierInitialCharacterToAdd::[]
| a::_ ->
  if in_dec (=) a jsAllowedIdentifierInitialCharacters
  then ident
  else jsIdentifierInitialCharacterToAdd::ident

(** val jsIdentifierSanitizeChar : char -> char **)

let jsIdentifierSanitizeChar a =
  if in_dec (=) a jsAllowedIdentifierCharacters
  then a
  else jsIdenitiferCharacterForReplacement

(** val jsIdentifierSanitizeBody : char list -> char list **)

let jsIdentifierSanitizeBody ident =
  map_string jsIdentifierSanitizeChar ident

(** val jsIdentifierSanitize : char list -> char list **)

let jsIdentifierSanitize ident =
  jsIdentifierFixInitial (jsIdentifierSanitizeBody ident)

(** val javaAllowedIdentifierInitialCharacters : char list **)

let javaAllowedIdentifierInitialCharacters =
  'A' :: ('B' :: ('C' :: ('D' :: ('E' :: ('F' :: ('G' :: ('H' :: ('I' :: ('J' :: ('K' :: ('L' :: ('M' :: ('N' :: ('O' :: ('P' :: ('Q' :: ('R' :: ('S' :: ('T' :: ('U' :: ('V' :: ('W' :: ('X' :: ('Y' :: ('Z' :: ('a' :: ('b' :: ('c' :: ('d' :: ('e' :: ('f' :: ('g' :: ('h' :: ('i' :: ('j' :: ('k' :: ('l' :: ('m' :: ('n' :: ('o' :: ('p' :: ('q' :: ('r' :: ('s' :: ('t' :: ('u' :: ('v' :: ('w' :: ('x' :: ('y' :: ('z' :: [])))))))))))))))))))))))))))))))))))))))))))))))))))

(** val javaAllowedIdentifierCharacters : char list **)

let javaAllowedIdentifierCharacters =
  'A' :: ('B' :: ('C' :: ('D' :: ('E' :: ('F' :: ('G' :: ('H' :: ('I' :: ('J' :: ('K' :: ('L' :: ('M' :: ('N' :: ('O' :: ('P' :: ('Q' :: ('R' :: ('S' :: ('T' :: ('U' :: ('V' :: ('W' :: ('X' :: ('Y' :: ('Z' :: ('a' :: ('b' :: ('c' :: ('d' :: ('e' :: ('f' :: ('g' :: ('h' :: ('i' :: ('j' :: ('k' :: ('l' :: ('m' :: ('n' :: ('o' :: ('p' :: ('q' :: ('r' :: ('s' :: ('t' :: ('u' :: ('v' :: ('w' :: ('x' :: ('y' :: ('z' :: ('0' :: ('1' :: ('2' :: ('3' :: ('4' :: ('5' :: ('6' :: ('7' :: ('8' :: ('9' :: ('_' :: ('$' :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val javaIdentifierInitialCharacterToAdd : char **)

let javaIdentifierInitialCharacterToAdd =
  'X'

(** val javaIdenitiferCharacterForReplacement : char **)

let javaIdenitiferCharacterForReplacement =
  'X'

(** val javaIdentifierFixInitial : char list -> char list **)

let javaIdentifierFixInitial ident = match ident with
| [] -> javaIdentifierInitialCharacterToAdd::[]
| a::_ ->
  if in_dec (=) a javaAllowedIdentifierInitialCharacters
  then ident
  else javaIdentifierInitialCharacterToAdd::ident

(** val javaIdentifierSanitizeChar : char -> char **)

let javaIdentifierSanitizeChar a =
  if in_dec (=) a javaAllowedIdentifierCharacters
  then a
  else javaIdenitiferCharacterForReplacement

(** val javaIdentifierSanitizeBody : char list -> char list **)

let javaIdentifierSanitizeBody ident =
  map_string javaIdentifierSanitizeChar ident

(** val javaIdentifierSanitize : char list -> char list **)

let javaIdentifierSanitize ident =
  javaIdentifierFixInitial (javaIdentifierSanitizeBody ident)

(** val javaSafeSeparator : char list **)

let javaSafeSeparator =
  '_'::[]

(** val javaAvoidList : char list list **)

let javaAvoidList =
  ('a'::('b'::('s'::('t'::('r'::('a'::('c'::('t'::[])))))))) :: (('a'::('s'::('s'::('e'::('r'::('t'::[])))))) :: (('b'::('o'::('o'::('l'::('e'::('a'::('n'::[]))))))) :: (('b'::('r'::('e'::('a'::('k'::[]))))) :: (('b'::('y'::('t'::('e'::[])))) :: (('c'::('a'::('s'::('e'::[])))) :: (('c'::('a'::('t'::('c'::('h'::[]))))) :: (('c'::('h'::('a'::('r'::[])))) :: (('c'::('l'::('a'::('s'::('s'::[]))))) :: (('c'::('o'::('n'::('s'::('t'::[]))))) :: (('c'::('o'::('n'::('t'::('i'::('n'::('u'::('e'::[])))))))) :: (('d'::('e'::('f'::('a'::('u'::('l'::('t'::[]))))))) :: (('d'::('o'::[])) :: (('d'::('o'::('u'::('b'::('l'::('e'::[])))))) :: (('e'::('l'::('s'::('e'::[])))) :: (('e'::('n'::('u'::('m'::[])))) :: (('e'::('x'::('t'::('e'::('n'::('d'::('s'::[]))))))) :: (('f'::('a'::('l'::('s'::('e'::[]))))) :: (('f'::('i'::('n'::('a'::('l'::[]))))) :: (('f'::('i'::('n'::('a'::('l'::('l'::('y'::[]))))))) :: (('f'::('l'::('o'::('a'::('t'::[]))))) :: (('f'::('o'::('r'::[]))) :: (('g'::('o'::('t'::('o'::[])))) :: (('i'::('f'::[])) :: (('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::[])))))))))) :: (('i'::('m'::('p'::('o'::('r'::('t'::[])))))) :: (('i'::('n'::('s'::('t'::('a'::('n'::('c'::('e'::('o'::('f'::[])))))))))) :: (('i'::('n'::('t'::[]))) :: (('i'::('n'::('t'::('e'::('r'::('f'::('a'::('c'::('e'::[]))))))))) :: (('l'::('o'::('n'::('g'::[])))) :: (('n'::('a'::('t'::('i'::('v'::('e'::[])))))) :: (('n'::('e'::('w'::[]))) :: (('n'::('u'::('l'::('l'::[])))) :: (('p'::('a'::('c'::('k'::('a'::('g'::('e'::[]))))))) :: (('p'::('r'::('i'::('v'::('a'::('t'::('e'::[]))))))) :: (('p'::('r'::('o'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))) :: (('p'::('u'::('b'::('l'::('i'::('c'::[])))))) :: (('r'::('e'::('t'::('u'::('r'::('n'::[])))))) :: (('s'::('h'::('o'::('r'::('t'::[]))))) :: (('s'::('t'::('a'::('t'::('i'::('c'::[])))))) :: (('s'::('t'::('r'::('i'::('c'::('t'::('f'::('p'::[])))))))) :: (('s'::('u'::('p'::('e'::('r'::[]))))) :: (('s'::('w'::('i'::('t'::('c'::('h'::[])))))) :: (('s'::('y'::('n'::('c'::('h'::('r'::('o'::('n'::('i'::('z'::('e'::('d'::[])))))))))))) :: (('t'::('h'::('i'::('s'::[])))) :: (('t'::('h'::('r'::('o'::('w'::[]))))) :: (('t'::('h'::('r'::('o'::('w'::('s'::[])))))) :: (('t'::('r'::('a'::('n'::('s'::('i'::('e'::('n'::('t'::[]))))))))) :: (('t'::('r'::('u'::('e'::[])))) :: (('t'::('r'::('y'::[]))) :: (('v'::('o'::('i'::('d'::[])))) :: (('v'::('o'::('l'::('a'::('t'::('i'::('l'::('e'::[])))))))) :: (('w'::('h'::('i'::('l'::('e'::[]))))) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))
