open Ascii
open List0
open NativeString
open String0
open StringAdd

val eol_newline : char list

val neol_newline : nstring

val quotel_double : char list

val nquotel_double : nstring

val indent : int -> nstring

val string_bracket : char list -> char list -> char list -> char list

val nstring_bracket : nstring -> nstring -> nstring -> nstring

val jsAllowedIdentifierInitialCharacters : char list

val jsAllowedIdentifierCharacters : char list

val jsIdentifierInitialCharacterToAdd : char

val jsIdenitiferCharacterForReplacement : char

val jsIdentifierFixInitial : char list -> char list

val jsIdentifierSanitizeChar : char -> char

val jsIdentifierSanitizeBody : char list -> char list

val jsIdentifierSanitize : char list -> char list

val javaAllowedIdentifierInitialCharacters : char list

val javaAllowedIdentifierCharacters : char list

val javaIdentifierInitialCharacterToAdd : char

val javaIdenitiferCharacterForReplacement : char

val javaIdentifierFixInitial : char list -> char list

val javaIdentifierSanitizeChar : char -> char

val javaIdentifierSanitizeBody : char list -> char list

val javaIdentifierSanitize : char list -> char list

val javaSafeSeparator : char list

val javaAvoidList : char list list
