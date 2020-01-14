open BrandRelation
open CoqLibAdd
open EJson
open EmitUtil
open Encode
open ForeignEJson
open ForeignEJsonRuntime
open List0
open String0
open ToString

type 'foreign_ejson_runtime_op ejson_runtime_op =
| EJsonRuntimeEqual
| EJsonRuntimeCompare
| EJsonRuntimeToString
| EJsonRuntimeToText
| EJsonRuntimeRecConcat
| EJsonRuntimeRecMerge
| EJsonRuntimeRecRemove
| EJsonRuntimeRecProject
| EJsonRuntimeRecDot
| EJsonRuntimeArray
| EJsonRuntimeArrayLength
| EJsonRuntimeArrayPush
| EJsonRuntimeArrayAccess
| EJsonRuntimeEither
| EJsonRuntimeToLeft
| EJsonRuntimeToRight
| EJsonRuntimeUnbrand
| EJsonRuntimeCast
| EJsonRuntimeDistinct
| EJsonRuntimeSingleton
| EJsonRuntimeFlatten
| EJsonRuntimeUnion
| EJsonRuntimeMinus
| EJsonRuntimeMin
| EJsonRuntimeMax
| EJsonRuntimeNth
| EJsonRuntimeCount
| EJsonRuntimeContains
| EJsonRuntimeSort
| EJsonRuntimeGroupBy
| EJsonRuntimeLength
| EJsonRuntimeSubstring
| EJsonRuntimeSubstringEnd
| EJsonRuntimeStringJoin
| EJsonRuntimeLike
| EJsonRuntimeNatLt
| EJsonRuntimeNatLe
| EJsonRuntimeNatPlus
| EJsonRuntimeNatMinus
| EJsonRuntimeNatMult
| EJsonRuntimeNatDiv
| EJsonRuntimeNatRem
| EJsonRuntimeNatAbs
| EJsonRuntimeNatLog2
| EJsonRuntimeNatSqrt
| EJsonRuntimeNatMinPair
| EJsonRuntimeNatMaxPair
| EJsonRuntimeNatSum
| EJsonRuntimeNatMin
| EJsonRuntimeNatMax
| EJsonRuntimeNatArithMean
| EJsonRuntimeFloatOfNat
| EJsonRuntimeFloatSum
| EJsonRuntimeFloatArithMean
| EJsonRuntimeFloatMin
| EJsonRuntimeFloatMax
| EJsonRuntimeNatOfFloat
| EJsonRuntimeForeign of 'foreign_ejson_runtime_op

(** val string_of_ejson_runtime_op :
    'a1 foreign_ejson -> ('a2, 'a1) foreign_ejson_runtime -> 'a2
    ejson_runtime_op -> char list **)

let string_of_ejson_runtime_op _ fejruntime = function
| EJsonRuntimeEqual -> 'e'::('q'::('u'::('a'::('l'::[]))))
| EJsonRuntimeCompare -> 'c'::('o'::('m'::('p'::('a'::('r'::('e'::[]))))))
| EJsonRuntimeToString ->
  't'::('o'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))
| EJsonRuntimeToText -> 't'::('o'::('T'::('e'::('x'::('t'::[])))))
| EJsonRuntimeRecConcat ->
  'r'::('e'::('c'::('C'::('o'::('n'::('c'::('a'::('t'::[]))))))))
| EJsonRuntimeRecMerge ->
  'r'::('e'::('c'::('M'::('e'::('r'::('g'::('e'::[])))))))
| EJsonRuntimeRecRemove ->
  'r'::('e'::('c'::('R'::('e'::('m'::('o'::('v'::('e'::[]))))))))
| EJsonRuntimeRecProject ->
  'r'::('e'::('c'::('P'::('r'::('o'::('j'::('e'::('c'::('t'::[])))))))))
| EJsonRuntimeRecDot -> 'r'::('e'::('c'::('D'::('o'::('t'::[])))))
| EJsonRuntimeArray -> 'a'::('r'::('r'::('a'::('y'::[]))))
| EJsonRuntimeArrayLength ->
  'a'::('r'::('r'::('a'::('y'::('L'::('e'::('n'::('g'::('t'::('h'::[]))))))))))
| EJsonRuntimeArrayPush ->
  'a'::('r'::('r'::('a'::('y'::('P'::('u'::('s'::('h'::[]))))))))
| EJsonRuntimeArrayAccess ->
  'a'::('r'::('r'::('a'::('y'::('A'::('c'::('c'::('e'::('s'::('s'::[]))))))))))
| EJsonRuntimeEither -> 'e'::('i'::('t'::('h'::('e'::('r'::[])))))
| EJsonRuntimeToLeft -> 't'::('o'::('L'::('e'::('f'::('t'::[])))))
| EJsonRuntimeToRight -> 't'::('o'::('R'::('i'::('g'::('h'::('t'::[]))))))
| EJsonRuntimeUnbrand -> 'u'::('n'::('b'::('r'::('a'::('n'::('d'::[]))))))
| EJsonRuntimeCast -> 'c'::('a'::('s'::('t'::[])))
| EJsonRuntimeDistinct ->
  'd'::('i'::('s'::('t'::('i'::('n'::('c'::('t'::[])))))))
| EJsonRuntimeSingleton ->
  's'::('i'::('n'::('g'::('l'::('e'::('t'::('o'::('n'::[]))))))))
| EJsonRuntimeFlatten -> 'f'::('l'::('a'::('t'::('t'::('e'::('n'::[]))))))
| EJsonRuntimeUnion -> 'u'::('n'::('i'::('o'::('n'::[]))))
| EJsonRuntimeMinus -> 'm'::('i'::('n'::('u'::('s'::[]))))
| EJsonRuntimeMin -> 'm'::('i'::('n'::[]))
| EJsonRuntimeMax -> 'm'::('a'::('x'::[]))
| EJsonRuntimeNth -> 'n'::('t'::('h'::[]))
| EJsonRuntimeCount -> 'c'::('o'::('u'::('n'::('t'::[]))))
| EJsonRuntimeContains ->
  'c'::('o'::('n'::('t'::('a'::('i'::('n'::('s'::[])))))))
| EJsonRuntimeSort -> 's'::('o'::('r'::('t'::[])))
| EJsonRuntimeGroupBy -> 'g'::('r'::('o'::('u'::('p'::('B'::('y'::[]))))))
| EJsonRuntimeLength -> 'l'::('e'::('n'::('g'::('t'::('h'::[])))))
| EJsonRuntimeSubstring ->
  's'::('u'::('b'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))
| EJsonRuntimeSubstringEnd ->
  's'::('u'::('b'::('s'::('t'::('r'::('i'::('n'::('g'::('E'::('n'::('d'::[])))))))))))
| EJsonRuntimeStringJoin ->
  's'::('t'::('r'::('i'::('n'::('g'::('J'::('o'::('i'::('n'::[])))))))))
| EJsonRuntimeLike -> 'l'::('i'::('k'::('e'::[])))
| EJsonRuntimeNatLt -> 'n'::('a'::('t'::('L'::('t'::[]))))
| EJsonRuntimeNatLe -> 'n'::('a'::('t'::('L'::('e'::[]))))
| EJsonRuntimeNatPlus -> 'n'::('a'::('t'::('P'::('l'::('u'::('s'::[]))))))
| EJsonRuntimeNatMinus ->
  'n'::('a'::('t'::('M'::('i'::('n'::('u'::('s'::[])))))))
| EJsonRuntimeNatMult -> 'n'::('a'::('t'::('M'::('u'::('l'::('t'::[]))))))
| EJsonRuntimeNatDiv -> 'n'::('a'::('t'::('D'::('i'::('v'::[])))))
| EJsonRuntimeNatRem -> 'n'::('a'::('t'::('R'::('e'::('m'::[])))))
| EJsonRuntimeNatAbs -> 'n'::('a'::('t'::('A'::('b'::('s'::[])))))
| EJsonRuntimeNatLog2 -> 'n'::('a'::('t'::('L'::('o'::('g'::('2'::[]))))))
| EJsonRuntimeNatSqrt -> 'n'::('a'::('t'::('S'::('q'::('r'::('t'::[]))))))
| EJsonRuntimeNatMinPair ->
  'n'::('a'::('t'::('M'::('i'::('n'::('P'::('a'::('i'::('r'::[])))))))))
| EJsonRuntimeNatMaxPair ->
  'n'::('a'::('t'::('M'::('a'::('x'::('P'::('a'::('i'::('r'::[])))))))))
| EJsonRuntimeNatSum -> 'n'::('a'::('t'::('S'::('u'::('m'::[])))))
| EJsonRuntimeNatMin -> 'n'::('a'::('t'::('M'::('i'::('n'::[])))))
| EJsonRuntimeNatMax -> 'n'::('a'::('t'::('M'::('a'::('x'::[])))))
| EJsonRuntimeNatArithMean ->
  'n'::('a'::('t'::('A'::('r'::('i'::('t'::('h'::('M'::('e'::('a'::('n'::[])))))))))))
| EJsonRuntimeFloatOfNat ->
  'f'::('l'::('o'::('a'::('t'::('O'::('f'::('N'::('a'::('t'::[])))))))))
| EJsonRuntimeFloatSum ->
  'f'::('l'::('o'::('a'::('t'::('S'::('u'::('m'::[])))))))
| EJsonRuntimeFloatArithMean ->
  'f'::('l'::('o'::('a'::('t'::('A'::('r'::('i'::('t'::('h'::('M'::('e'::('a'::('n'::[])))))))))))))
| EJsonRuntimeFloatMin ->
  'f'::('l'::('o'::('a'::('t'::('M'::('i'::('n'::[])))))))
| EJsonRuntimeFloatMax ->
  'f'::('l'::('o'::('a'::('t'::('M'::('a'::('x'::[])))))))
| EJsonRuntimeNatOfFloat ->
  'n'::('a'::('t'::('O'::('f'::('F'::('l'::('o'::('a'::('t'::[])))))))))
| EJsonRuntimeForeign fop ->
  toString fejruntime.foreign_ejson_runtime_op_tostring fop

(** val defaultEJsonToString : 'a1 foreign_ejson -> 'a1 ejson -> char list **)

let rec defaultEJsonToString fejson = function
| Coq_ejnull -> 'u'::('n'::('i'::('t'::[])))
| Coq_ejnumber n -> toString coq_ToString_float n
| Coq_ejbigint n -> toString coq_ToString_Z n
| Coq_ejbool b -> toString coq_ToString_bool b
| Coq_ejstring s -> stringToString s
| Coq_ejarray l ->
  string_bracket ('['::[])
    (concat (','::(' '::[])) (map (defaultEJsonToString fejson) l)) (']'::[])
| Coq_ejobject r ->
  (match r with
   | [] ->
     string_bracket ('{'::[])
       (concat (','::(' '::[]))
         (map (fun xy ->
           let (x, y) = xy in
           append (stringToString (key_decode x))
             (append ('-'::('>'::[])) (defaultEJsonToString fejson y))) r))
       ('}'::[])
   | p :: l ->
     let (s1, j') = p in
     (match j' with
      | Coq_ejnull ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejnumber _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejbigint _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejbool _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejstring _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejarray j1 ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | p0 :: l0 ->
           let (s2, j2) = p0 in
           (match l0 with
            | [] ->
              if string_dec s1 ('$'::('c'::('l'::('a'::('s'::('s'::[]))))))
              then if string_dec s2 ('$'::('d'::('a'::('t'::('a'::[])))))
                   then (match ejson_brands j1 with
                         | Some br ->
                           string_bracket ('<'::[])
                             (append (toString coq_ToString_brands br)
                               (append (':'::[])
                                 (defaultEJsonToString fejson j2))) ('>'::[])
                         | None ->
                           string_bracket ('{'::[])
                             (concat (','::(' '::[]))
                               ((append (stringToString (key_decode s1))
                                  (append ('-'::('>'::[]))
                                    (string_bracket ('['::[])
                                      (concat (','::(' '::[]))
                                        (map (defaultEJsonToString fejson) j1))
                                      (']'::[])))) :: ((append
                                                         (stringToString
                                                           (key_decode s2))
                                                         (append
                                                           ('-'::('>'::[]))
                                                           (defaultEJsonToString
                                                             fejson j2))) :: [])))
                             ('}'::[]))
                   else string_bracket ('{'::[])
                          (concat (','::(' '::[]))
                            ((append (stringToString (key_decode s1))
                               (append ('-'::('>'::[]))
                                 (string_bracket ('['::[])
                                   (concat (','::(' '::[]))
                                     (map (defaultEJsonToString fejson) j1))
                                   (']'::[])))) :: ((append
                                                      (stringToString
                                                        (key_decode s2))
                                                      (append
                                                        ('-'::('>'::[]))
                                                        (defaultEJsonToString
                                                          fejson j2))) :: [])))
                          ('}'::[])
              else string_bracket ('{'::[])
                     (concat (','::(' '::[]))
                       ((append (stringToString (key_decode s1))
                          (append ('-'::('>'::[]))
                            (string_bracket ('['::[])
                              (concat (','::(' '::[]))
                                (map (defaultEJsonToString fejson) j1))
                              (']'::[])))) :: ((append
                                                 (stringToString
                                                   (key_decode s2))
                                                 (append ('-'::('>'::[]))
                                                   (defaultEJsonToString
                                                     fejson j2))) :: [])))
                     ('}'::[])
            | _ :: _ ->
              string_bracket ('{'::[])
                (concat (','::(' '::[]))
                  (map (fun xy ->
                    let (x, y) = xy in
                    append (stringToString (key_decode x))
                      (append ('-'::('>'::[]))
                        (defaultEJsonToString fejson y))) r)) ('}'::[])))
      | Coq_ejobject _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))
      | Coq_ejforeign _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then string_bracket ('L'::('e'::('f'::('t'::('('::[])))))
                  (defaultEJsonToString fejson j') (')'::[])
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then string_bracket
                       ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
                       (defaultEJsonToString fejson j') (')'::[])
                else string_bracket ('{'::[])
                       (concat (','::(' '::[]))
                         (map (fun xy ->
                           let (x, y) = xy in
                           append (stringToString (key_decode x))
                             (append ('-'::('>'::[]))
                               (defaultEJsonToString fejson y))) ((s1,
                           j') :: []))) ('}'::[])
         | _ :: _ ->
           string_bracket ('{'::[])
             (concat (','::(' '::[]))
               (map (fun xy ->
                 let (x, y) = xy in
                 append (stringToString (key_decode x))
                   (append ('-'::('>'::[])) (defaultEJsonToString fejson y)))
                 r)) ('}'::[]))))
| Coq_ejforeign fd -> toString fejson.foreign_ejson_tostring fd
