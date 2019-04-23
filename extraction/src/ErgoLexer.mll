(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

{
  open Util
  open LexUtil
  open ErgoParser

  let keyword_table =
    let tbl = Hashtbl.create 39 in
    begin
      List.iter (fun (key, data) -> Hashtbl.add tbl key data)
	      [ (* declarations *)
	      "namespace", NAMESPACE;
	      "import", IMPORT;
	      "define", DEFINE;
	      "function", FUNCTION;
        (* types *)
	      "abstract", ABSTRACT;
	      "transaction", TRANSACTION;
	      "concept", CONCEPT;
	      "event", EVENT;
	      "asset", ASSET;
	      "participant", PARTICIPANT;
	      "enum", ENUM;
	      "extends", EXTENDS;
        (* contract *)
	      "contract", CONTRACT;
	      "over", OVER;
	      "clause", CLAUSE;
	      "emits", EMITS;
	      "state", STATE;
	      "call", CALL;
	      "send", SEND;
	      (* Expressions *)
 	      "enforce", ENFORCE;
	      "if", IF;
	      "then", THEN;
	      "else", ELSE;
	      "let", LET;
	      "info", INFO;
	      "foreach", FOREACH;
	      "return", RETURN;
	      "in", IN;
	      "where", WHERE;
	      "throw", THROW;
	      "constant", CONSTANT;
	      "match", MATCH;
	      "set",SET;
        "emit",EMIT;
	      "with", WITH;
        "or", OR;
        "and", AND;
	      (* Data *)
	      "true", TRUE;
	      "false", FALSE;
	      "unit", UNIT;
	      "none", NONE;
        "some", SOME;
        "nan", FLOAT nan;
        "infinity", FLOAT infinity;
	    ]; tbl
    end

  let char_for_backslash c =
  begin match c with
  | 'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c   -> c
  end

  let decimal_code  c d u =
    100 * (Char.code c - 48) + 10 * (Char.code d - 48) + (Char.code u - 48)
}

let newline = ('\010' | '\013' | "\013\010")
let letter = ['A'-'Z' 'a'-'z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']

let backslash_escapes =
  ['\\' '"' 'n' 't' 'b' 'r']

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit+ (frac exp? | exp)
let int = ['0'-'9']+

rule token lh = parse
| eof { EOF }
| "=" { EQUAL }
| "!" { NOT }
| "!=" { NEQUAL }
| "<" { LT }
| ">" { GT }
| "<=" { LTEQ }
| ">=" { GTEQ }
| "+" { PLUS }
| "++" { PLUSPLUS }
| "*" { STAR }
| "^" { CARROT }
| "/" { SLASH }
| "%" { PERCENT }
| "-" { MINUS }
| "," { COMMA }
| ":" { COLON }
| "?." { QUESTIONDOT }
| "." { DOT }
| ";" { SEMI }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LCURLY }
| "}" { RCURLY }
| "??" { QUESTIONQUESTION }
| "?" { QUESTION }
| "~" { TILDE }
| "_" { UNDERSCORE }
| [' ' '\t']
    { token lh lexbuf }
| newline
    { Lexing.new_line lexbuf; token lh lexbuf }
| letter identchar*
    { let s = Lexing.lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> IDENT s }
| float as f
    { FLOAT (float_of_string f) }
| int as i
    { INT (int_of_string i) }
| '"'
    { let string_start = lexbuf.lex_start_p in
      lh_reset_string lh; string lh lexbuf;
      lexbuf.lex_start_p <- string_start;
      let s = lh_get_string lh in STRING s }
| "{{"
    { lh_reset_string lh;
      lh_push_state lh TextState;
      OPENTEXT }
| "}}"
    { lh_reset_string lh;
      ignore(lh_pop_state lh);
      CLOSEEXPR }
| "/*"
    { comment 1 lexbuf; token lh lexbuf }
| "//"
    { linecomment lexbuf; token lh lexbuf }
| _
    { raise (LexError (Printf.sprintf "At offset %d: unexpected character" (Lexing.lexeme_start lexbuf))) }

and string lh = parse
  | '"'    { () }  (* End of string *)
  | '\\' (['0'-'9'] as c) (['0'-'9'] as d) (['0'-'9']  as u)
    { let v = decimal_code c d u in
      if v > 255 then
        raise (LexError (Printf.sprintf "illegal ascii code: '\\%c%c%c'" c d u))
      else lh_add_char_to_string lh (Char.chr v); string lh lexbuf }
  | '\\' (backslash_escapes as c) { lh_add_char_to_string lh (char_for_backslash c); string lh lexbuf }
  | eof    { raise (LexError "String not terminated.") }
  | newline
      { Lexing.new_line lexbuf; lh_add_char_to_string lh (Lexing.lexeme_char lexbuf 0); string lh lexbuf }
  | _      { lh_add_char_to_string lh (Lexing.lexeme_char lexbuf 0); string lh lexbuf }

and comment cpt = parse
  | "/*"
      { comment (cpt + 1) lexbuf }
  | "*/"
      { if cpt > 1 then comment (cpt - 1) lexbuf }
  | eof
      { raise (LexError "Unterminated comment") }
  | newline
      { Lexing.new_line lexbuf; comment cpt lexbuf }
  | _
      { comment cpt lexbuf }

and linecomment = parse
  | eof
      { () }
  | newline
      { Lexing.new_line lexbuf; () }
  | _
      { linecomment lexbuf }

and text lh = parse
| "{{" { lh_push_state lh ExprState; OPENEXPR (lh_get_string lh) }
| "}}" { ignore(lh_pop_state lh); CLOSETEXT (lh_get_string lh) }
| "[{" { lh_push_state lh VarState; OPENVAR (lh_get_string lh) }
| '\\' (['0'-'9'] as c) (['0'-'9'] as d) (['0'-'9']  as u)
    { let v = decimal_code c d u in
    if v > 255 then
      raise (LexError (Printf.sprintf "illegal ascii code: '\\%c%c%c'" c d u))
    else lh_add_char_to_string lh(Char.chr v); text lh lexbuf }
| '\\' (backslash_escapes as c) { lh_add_char_to_string lh (char_for_backslash c); text lh lexbuf }
| eof    { if lh_in_template lh
           then begin ignore(lh_pop_state lh); CLOSETEXT (lh_get_string lh) end
           else raise (LexError "Text not terminated.\n") }
| newline
    { Lexing.new_line lexbuf; lh_add_char_to_string lh (Lexing.lexeme_char lexbuf 0); text lh lexbuf }
| _      { lh_add_char_to_string lh (Lexing.lexeme_char lexbuf 0); text lh lexbuf }

and var lh = parse
| eof { EOF }
| "as" { AS }
| ":?" { COLONQUESTION }
| [' ' '\t']
    { var lh lexbuf }
| newline
    { Lexing.new_line lexbuf; token lh lexbuf }
| letter identchar*
    { let s = Lexing.lexeme lexbuf in
      IDENT s }
| '"'
    { let string_start = lexbuf.lex_start_p in
      lh_reset_string lh; string lh lexbuf;
      lexbuf.lex_start_p <- string_start;
      let s = lh_get_string lh in STRING s }
| "}]"
    { lh_reset_string lh;
      ignore(lh_pop_state lh);
      CLOSEVAR }
