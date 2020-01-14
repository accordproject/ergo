open Ascii
open FloatAdd
open JavaScript
open JavaScriptAst
open JsNumber
open JsSyntax
open List0
open Nat
open NativeString

val eol : nstring

val quotel : nstring

val indent : int -> nstring

val comma_list_string : char list list -> nstring

val comma_list : nstring list -> nstring

val js_quote_char : char -> nstring

val js_quote_string : char list -> nstring

val js_quote_number : number -> nstring

val nstring_of_literal : literal -> nstring

val nstring_of_propname : propname -> nstring

val nstring_of_expr : expr -> int -> nstring

val nstring_of_stat : stat -> int -> nstring

val nstring_of_element : element -> int -> nstring

val nstring_of_prog : prog -> int -> nstring

val nstring_of_funcbody : funcbody -> int -> nstring

val nstring_of_method : funcdecl -> int -> nstring

val nstring_of_decl : topdecl -> nstring

val js_ast_to_js_top : js_ast -> javascript
