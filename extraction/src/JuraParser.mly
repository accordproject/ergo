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

%{
  open Util
  open JComp
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token PACKAGE IMPORT DEFINITION
%token CONTRACT OVER CLAUSE THROWS

%token IF GUARD ELSE
%token RETURN THROW
%token LET AS
%token NEW THIS
%token SWITCH TYPESWITCH CASE DEFAULT

%token OR AND NOT
%token FLATTEN
%token AVG FAVG SUM FSUM COUNT MIN MAX

%token NIL
%token TRUE FALSE

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS MINUS STAR SLASH
%token DOT COMMA COLON SEMI
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LCURLY RCURLY
%token EOF

%left RCURLY
%left SEMI
%left RETURN
%right AND OR
%right NOT
%right EQUAL NEQUAL
%right LT GT LTEQ GTEQ
%right PLUS MINUS
%right STAR SLASH
%left DOT

%start <JComp.JuraCompiler.jura_package> main

%%

main:
| p = package EOF
    { p }

package:
| pname = packagedecl ss = stmts
    { { package_name = pname;
	package_statements = ss; } }

packagedecl:
| PACKAGE qn = qname_prefix
    { qn }

stmts:
|
    { [] }
| s = stmt ss = stmts
    { s :: ss }

stmt:
| DEFINITION v = safeident EQUAL e = expr
    { JGlobal (v, e) }
| DEFINITION cn = IDENT LPAREN RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { JFunc
	{ func_name = Util.char_list_of_string cn;
	  func_closure =
	  { closure_params = [];
            closure_output = Some (Util.char_list_of_string out);
	    closure_throw = mt;
	    closure_body = e; } } }
| DEFINITION cn = IDENT LPAREN ps = params RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { JFunc
	{ func_name = Util.char_list_of_string cn;
	  func_closure =
	  { closure_params = ps;
            closure_output = Some (Util.char_list_of_string out);
	    closure_throw = mt;
	    closure_body = e; } } }
| IMPORT qn = qname_prefix
    { JImport qn }
| c = contract
    { JContract c }

contract:
| CONTRACT cn = IDENT OVER tn = IDENT LCURLY ds = declarations RCURLY
    { { contract_name = Util.char_list_of_string cn;
        contract_template = Util.char_list_of_string tn;
        contract_declarations = ds; } }

declarations:
| 
    { [] }
| f = func ds = declarations
    { (Func f) :: ds }
| cl = clause ds = declarations
    { (Clause cl) :: ds }

func:
| DEFINITION cn = IDENT LPAREN RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { { func_name = Util.char_list_of_string cn;
	func_closure =
	{ closure_params = [];
          closure_output = Some (Util.char_list_of_string out);
	  closure_throw = mt;
	  closure_body = e; } } }
| DEFINITION cn = IDENT LPAREN ps = params RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { { func_name = Util.char_list_of_string cn;
	func_closure =
	{ closure_params = ps;
          closure_output = Some (Util.char_list_of_string out);
	  closure_throw = mt;
	  closure_body = e; } } }

clause:
| CLAUSE cn = IDENT LPAREN RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { { clause_name = Util.char_list_of_string cn;
	clause_closure =
	  { closure_params = [];
            closure_output = Some (Util.char_list_of_string out);
	    closure_throw = mt;
	    closure_body = e; } } }
| CLAUSE cn = IDENT LPAREN ps = params RPAREN out = IDENT mt = maythrow LCURLY e = expr RCURLY
    { { clause_name = Util.char_list_of_string cn;
	clause_closure =
	  { closure_params = ps;
            closure_output = Some (Util.char_list_of_string out);
	    closure_throw = mt;
	    closure_body = e; } } }

maythrow:
|
  { None }
| THROWS en = IDENT
  { Some (Util.char_list_of_string en) }
    
params:
| p = param
    { p :: [] }
| p = param COMMA ps = params
    { p :: ps }

param:
| pn = IDENT pt = IDENT (* XXX Has to be fixed so type name is passed as well *)
    { (Util.char_list_of_string pn,Some (Util.char_list_of_string pt)) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { JuraCompiler.jfuncall (Util.char_list_of_string fn) el }
(* Constants *)
| NIL
    { JuraCompiler.jconst JuraCompiler.Data.dunit }
| TRUE
    { JuraCompiler.jconst (JuraCompiler.Data.dbool true) }
| FALSE
    { JuraCompiler.jconst (JuraCompiler.Data.dbool false) }
| i = INT
    { JuraCompiler.jconst (JuraCompiler.Data.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { JuraCompiler.jconst (JuraCompiler.Enhanced.Data.dfloat f) }
| s = STRING
    { JuraCompiler.jconst (JuraCompiler.Data.dstring (Util.char_list_of_string s)) }
| LBRACKET el = exprlist RBRACKET
    { JuraCompiler.jarray el }
(* Expressions *)
| v = IDENT
    { JuraCompiler.jvar (Util.char_list_of_string v) }
| e = expr DOT a = IDENT
    { JuraCompiler.jdot (Util.char_list_of_string a) e }
| IF e1 = expr LCURLY e2 = expr RCURLY ELSE e3 = else_clause
    { JuraCompiler.jif e1 e2 e3 }
| GUARD e1 = expr ELSE LCURLY e3 = expr RCURLY e2 = expr
    { JuraCompiler.jguard e1 e2 e3 }
| RETURN e = expr
    { JuraCompiler.jreturn e }
| THROW qn = qname LCURLY r = reclist RCURLY
    { JuraCompiler.jthrow (fst qn) (snd qn) r }
| NEW qn = qname LCURLY r = reclist RCURLY
    { JuraCompiler.jnew (fst qn) (snd qn) r }
| THIS
    { JuraCompiler.jthis }
| LET v = safeident EQUAL e1 = expr SEMI e2 = expr
    { JuraCompiler.jlet v e1 e2 }
| SWITCH e0 = expr LCURLY csd = cases RCURLY
    { JuraCompiler.jswitch e0 (fst csd) (snd csd) }
(* Functions *)
| NOT e = expr
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opneg e }
| FLATTEN LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opflatten e }
| AVG LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opnummean e }
| FAVG LPAREN e = expr RPAREN
    { JuraCompiler.junaryop (OpForeignUnary
		    (Obj.magic (Enhanced_unary_float_op
				  (Uop_float_arithmean)))) e }
| SUM LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opsum e }
| FSUM LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Enhanced.Ops.Unary.float_sum e }
| COUNT LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opcount e }
| MAX LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opnummax e }
| MIN LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opnummin e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opneg (JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opequal e1 e2) }
| e1 = expr LT e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.oplt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ople e1 e2 }
| e1 = expr GT e2 = expr
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opneg (JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ople e1 e2) }
| e1 = expr GTEQ e2 = expr
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opneg (JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.oplt e1 e2) }
| e1 = expr MINUS e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ZArith.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ZArith.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ZArith.opmult e1 e2 }
| e1 = expr SLASH e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.ZArith.opdiv e1 e2 }
| e1 = expr AND e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opor e1 e2 }

else_clause:
| LCURLY e = expr RCURLY
    { e }
| IF e1 = expr LCURLY e2 = expr RCURLY ELSE e3 = else_clause
    { JuraCompiler.jif e1 e2 e3 }

(* expression list *)
exprlist:
| 
    { [] }
| e = expr
    { [e] }
| e = expr COMMA el = exprlist
    { e :: el }

(* cases *)
cases:
| DEFAULT COLON e = expr
    { ([],e) }
| CASE d = data COLON e = expr cs = cases
    { (((None,JuraCompiler.jcasevalue d),e)::(fst cs), snd cs) }
| CASE LET v = safeident EQUAL d = data COLON e = expr cs = cases
    { (((Some v,JuraCompiler.jcasevalue d),e)::(fst cs), snd cs) }
| CASE AS brand = STRING COLON e = expr tcs = cases
    { (((None,JuraCompiler.jcasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }
| CASE LET v = safeident AS brand = STRING COLON e = expr tcs = cases
    { (((Some v,JuraCompiler.jcasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }

(* New struct *)
reclist:
| 
    { [] }
| r = recatt
    { [r] }
| r = recatt COMMA rl = reclist
    { r :: rl }

recatt:
| a = IDENT COLON e = expr
    { (Util.char_list_of_string a, e) }

(* Qualified name *)
qname_base:
| STAR
    { (None,"*") }
| i = safeident_base
    { (None,i) }
| i = safeident_base DOT q = qname_base
    { if i = "*"
      then raise (Jura_Error "'*' can only be last in a qualified name")
      else
        begin match q with
	| (None, last) -> (Some i, last)
	| (Some prefix, last) -> (Some (i ^ "." ^ prefix), last)
	end }

qname:
| qn = qname_base
    { begin match qn with
      | (None,last) -> (None,Util.char_list_of_string last)
      | (Some prefix, last) ->
	  (Some (Util.char_list_of_string prefix), Util.char_list_of_string last)
      end }

qname_prefix:
| qn = qname_base
    { begin match qn with
      | (None,last) -> Util.char_list_of_string last
      | (Some prefix, last) -> Util.char_list_of_string (prefix ^ "." ^ last)
      end }

(* data *)
data:
| s = STRING
    { JuraCompiler.Data.dstring (Util.char_list_of_string s) }
| i = INT
    { JuraCompiler.Data.dnat i }
| f = FLOAT
    { JuraCompiler.Enhanced.Data.dfloat f }
(* Safe identifier *)
safeident:
| i = safeident_base
    { Util.char_list_of_string i }

safeident_base:
| i = IDENT { i }
| PACKAGE { "package" }
| IMPORT { "import" }
| DEFINITION { "definition" }
| CONTRACT { "contract" }
| OVER { "over" }
| CLAUSE { "clause" }
| IF { "if" }
| GUARD { "guard" }
| ELSE { "else" }
| RETURN { "return" }
| THROW { "throw" }
| THROWS { "throws" }
| LET { "let" }
| AS { "as" }
| NEW { "new" }
| SWITCH { "switch" }
| TYPESWITCH { "typeswitch" }
| CASE { "case" }
| DEFAULT { "default" }
| THIS { "this" }
| OR { "or" }
| AND { "and" }
| NOT { "not" }
| FLATTEN { "flatten" }
| AVG { "avg" }
| FAVG { "favg" }
| SUM { "sum" }
| FSUM { "fsum" }
| COUNT { "count" }
| MIN { "min" }
| MAX { "max" }
| NIL { "nil" }
| TRUE { "true" }
| FALSE { "false" }

