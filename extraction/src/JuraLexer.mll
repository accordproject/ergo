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
  open JuraParser

  let keyword_table =
    let tbl = Hashtbl.create 39 in
    begin
      List.iter (fun (key, data) -> Hashtbl.add tbl key data)
	[ (* declarations *)
	  "package", PACKAGE;
	  "import", IMPORT;
          (* contract *)
	  "contract", CONTRACT;
	  "over", OVER;
	  "clause", CLAUSE;
	  "throws", THROWS;
	  (* Expressions *)
	  "if", IF;
	  "guard", GUARD;
	  "else", ELSE;
	  "return", RETURN;
	  "throw", THROW;
	  "new", NEW;
	  "this", THIS;
	  "let", LET;
	  (* Functions *)
	  "flatten", FLATTEN;
	  "avg", AVG;
	  "favg", FAVG;
	  "sum", SUM;
          "fsum", FSUM;
	  "count", COUNT;
	  "min", MIN;
	  "max", MAX;
	  (* Data *)
	  "true", TRUE;
	  "false", FALSE;
	  "nil", NIL
	]; tbl
    end

}

let newline = ('\010' | '\013' | "\013\010")
let letter = ['A'-'Z' 'a'-'z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* (frac exp? | exp)

rule token sbuff = parse
| eof { EOF }
| "=" { EQUAL }
| "!" { NOT }
| "!=" { NEQUAL }
| "<" { LT }
| ">" { GT }
| "<=" { LTEQ }
| ">=" { GTEQ }
| "+" { PLUS }
| "*" { STAR }
| "/" { SLASH }
| "-" { MINUS }
| "||" { OR }
| "&&" { AND }
| "," { COMMA }
| ":" { COLON }
| "." { DOT }
| ";" { SEMI }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LCURLY }
| "}" { RCURLY }
| [' ' '\t']
    { token sbuff lexbuf }
| newline
    { Lexing.new_line lexbuf; token sbuff lexbuf }
| float as f
    { FLOAT (float_of_string f) }
| ('-'? ['0'-'9']+) as i
    { INT (int_of_string i) }
| '"'
    { reset_string sbuff; string sbuff lexbuf }
| letter identchar*
    { let s = Lexing.lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> IDENT s }
| "/*"
    { comment 1 lexbuf; token sbuff lexbuf }
| "//"
    { linecomment lexbuf; token sbuff lexbuf }
| _
    { raise (LexError (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

and string sbuff = parse
  | "\"\"" { add_char_to_string sbuff '"'; string sbuff lexbuf }                         (* Escaped quote *)
  | "\013\n" { add_char_to_string sbuff '\n'; string sbuff lexbuf }
  | "\013" { add_char_to_string sbuff '\n'; string sbuff lexbuf }
  | '"'    { let s = get_string sbuff in STRING s }  (* End of string *)
  | eof    { raise (LexError "String not terminated.\n") }
  | _      { add_char_to_string sbuff (Lexing.lexeme_char lexbuf 0); string sbuff lexbuf }

and comment cpt = parse
  | "/*"
      { comment (cpt + 1) lexbuf }
  | "*/"
      { if cpt > 1 then comment (cpt - 1) lexbuf }
  | eof
      { raise (LexError "Unterminated comment\n") }
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

