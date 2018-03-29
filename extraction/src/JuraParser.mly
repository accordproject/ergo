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

%token NAMESPACE IMPORT DEFINE FUNCTION
%token CONCEPT TRANSACTION ENUM EXTENDS
%token CONTRACT OVER CLAUSE THROWS

%token ENFORCE IF THEN ELSE
%token LET FOR IN WHERE
%token RETURN THROW
%token VARIABLE AS
%token NEW
%token MATCH TYPEMATCH WITH

%token OR AND NOT
%token FLATTEN
%token AVG SUM COUNT MIN MAX

%token NIL
%token TRUE FALSE

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS MINUS STAR SLASH
%token PLUSPLUS
%token DOT COMMA COLON SEMI QUESTION
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LCURLY RCURLY
%token EOF

%left SEMI
%left ELSE
%left RETURN
%left OR
%left AND
%left EQUAL NEQUAL
%left LT GT LTEQ GTEQ
%left PLUS MINUS
%left STAR SLASH
%left PLUSPLUS
%right NOT
%left DOT

%start <JComp.JuraCompiler.jura_package> main

%%

main:
| p = package EOF
    { p }


package:
| ns = namespacedecl ss = stmts
    { { package_namespace = ns;
	package_statements = ss; } }

namespacedecl:
| /* empty */
    { None }
| NAMESPACE qn = qname_prefix
    { Some qn }

stmts:
|
    { [] }
| s = stmt ss = stmts
    { s :: ss }

stmt:
| DEFINE CONCEPT cn = ident dt = cto_class_decl
    { let (oe,ctype) = dt in JType (JuraCompiler.mk_cto_declaration (JuraCompiler.mk_class_ref None cn) (CTOConcept (oe,ctype))) }
| DEFINE TRANSACTION cn = ident dt = cto_class_decl
    { let (oe,ctype) = dt in JType (JuraCompiler.mk_cto_declaration (JuraCompiler.mk_class_ref None cn) (CTOTransaction (oe,ctype))) }
| DEFINE ENUM cn = ident et = cto_enum_decl
    { JType (JuraCompiler.mk_cto_declaration (JuraCompiler.mk_class_ref None cn) (CTOEnum et)) }
| DEFINE VARIABLE v = ident EQUAL e = expr
    { JGlobal (v, e) }
| DEFINE FUNCTION cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { JFunc
	{ func_name = cn;
	  func_closure =
	  { closure_params0 = [];
            closure_output0 = Some out;
	    closure_throw = mt;
	    closure_body0 = e; } } }
| DEFINE FUNCTION cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { JFunc
	{ func_name = cn;
	  func_closure =
	  { closure_params0 = ps;
            closure_output0 = Some out;
	    closure_throw = mt;
	    closure_body0 = e; } } }
| IMPORT qn = qname_prefix
    { JImport qn }
| c = contract
    { JContract c }

cto_class_decl:
| LCURLY rt = rectype RCURLY
    { (None, rt) }
| EXTENDS en = ident LCURLY rt = rectype RCURLY
    { (Some en, rt) }

cto_enum_decl:
| LCURLY il = identlist RCURLY
    { il }

contract:
| CONTRACT cn = ident OVER tn = ident LCURLY ds = declarations RCURLY
    { { contract_name = cn;
        contract_template = tn;
        contract_declarations = ds; } }

declarations:
| 
    { [] }
| f = func ds = declarations
    { (Func f) :: ds }
| cl = clause ds = declarations
    { (Clause cl) :: ds }

func:
| DEFINE FUNCTION cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { { func_name = cn;
	func_closure =
	{ closure_params0 = [];
          closure_output0 = Some out;
	  closure_throw = mt;
	  closure_body0 = e; } } }
| DEFINE FUNCTION cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { { func_name = cn;
	func_closure =
	{ closure_params0 = ps;
          closure_output0 = Some out;
	  closure_throw = mt;
	  closure_body0 = e; } } }

clause:
| CLAUSE cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { { clause_name = cn;
	clause_closure =
	  { closure_params0 = [];
            closure_output0 = Some out;
	    closure_throw = mt;
	    closure_body0 = e; } } }
| CLAUSE cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY e = expr RCURLY
    { { clause_name = cn;
	clause_closure =
	  { closure_params0 = ps;
            closure_output0 = Some out;
	    closure_throw = mt;
	    closure_body0 = e; } } }

maythrow:
|
  { None }
| THROWS en = ident
  { Some en }
    
params:
| p = param
    { p :: [] }
| p = param COMMA ps = params
    { p :: ps }

param:
| pn = IDENT
    { (Util.char_list_of_string pn, None) }
| pn = IDENT pt = paramtype
    { (Util.char_list_of_string pn, Some pt) }

paramtype:
| pt = IDENT
    { begin match pt with
      | "Boolean" -> JuraCompiler.cto_boolean
      | "String" -> JuraCompiler.cto_string
      | "Double" -> JuraCompiler.cto_double
      | "Long" -> JuraCompiler.cto_long
      | "Integer" -> JuraCompiler.cto_integer
      | "DateTime" -> JuraCompiler.cto_dateTime
      | _ -> JuraCompiler.cto_class_ref (JuraCompiler.mk_class_ref None (Util.char_list_of_string pt))
      end }
| LCURLY rt = rectype RCURLY
    { JuraCompiler.cto_record rt }
| pt = paramtype LBRACKET RBRACKET
    { JuraCompiler.cto_array pt }
| pt = paramtype QUESTION
    { JuraCompiler.cto_option pt }

rectype:
| 
    { [] }
| at = atttype
    { [at] }
| at = atttype COMMA rt = rectype
    { at :: rt }

atttype:
| an = IDENT COLON pt = paramtype
    { (Util.char_list_of_string an, pt) }

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
    { JuraCompiler.jconst (JuraCompiler.Data.dfloat f) }
| s = STRING
    { JuraCompiler.jconst (JuraCompiler.Data.dstring (Util.char_list_of_string s)) }
| LBRACKET el = exprlist RBRACKET
    { JuraCompiler.jarray el }
(* Expressions *)
| v = IDENT
    { JuraCompiler.jvar (Util.char_list_of_string v) }
| e = expr DOT a = safeident
    { JuraCompiler.jdot a e }
| IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { JuraCompiler.jif e1 e2 e3 }
| ENFORCE e1 = expr ELSE e3 = expr SEMI e2 = expr
    { JuraCompiler.jenforce e1 e2 e3 }
| ENFORCE e1 = expr SEMI e3 = expr
    { JuraCompiler.jenforce_default_fail e1 e3 }
| RETURN e = expr
    { JuraCompiler.jreturn e }
| THROW qn = qname LCURLY r = reclist RCURLY
    { JuraCompiler.jthrow (fst qn) (snd qn) r }
| NEW qn = qname LCURLY r = reclist RCURLY
    { JuraCompiler.jnew (fst qn) (snd qn) r }
| LCURLY r = reclist RCURLY
    { JuraCompiler.jrecord r }
| CONTRACT
    { JuraCompiler.jthis_contract }
| CLAUSE
    { JuraCompiler.jthis_clause }
| DEFINE VARIABLE v = ident EQUAL e1 = expr SEMI e2 = expr
    { JuraCompiler.jlet v e1 e2 }
| LET v = ident EQUAL e1 = expr SEMI e2 = expr
    { JuraCompiler.jlet v e1 e2 }
| DEFINE VARIABLE v = ident COLON t = paramtype EQUAL e1 = expr SEMI e2 = expr
    { JuraCompiler.jlet_typed v t e1 e2 }
| LET v = ident COLON t = paramtype EQUAL e1 = expr SEMI e2 = expr
    { JuraCompiler.jlet_typed v t e1 e2 }
| MATCH e0 = expr csd = cases
    { JuraCompiler.jmatch e0 (fst csd) (snd csd) }
| FOR v = ident IN e1 = expr LCURLY e2 = expr RCURLY
    { JuraCompiler.jfor v e1 None e2 }
| FOR v = ident IN e1 = expr WHERE econd = expr LCURLY e2 = expr RCURLY
    { JuraCompiler.jfor v e1 (Some econd) e2 }
(* Functions *)
| NOT e = expr
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opneg e }
| FLATTEN LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opflatten e }
| AVG LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opnummean e }
| SUM LPAREN e = expr RPAREN
    { JuraCompiler.junaryop JuraCompiler.Ops.Unary.opsum e }
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
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.Float.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.Float.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.Float.opmult e1 e2 }
| e1 = expr SLASH e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.Float.opdiv e1 e2 }
| e1 = expr AND e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opor e1 e2 }
| e1 = expr PLUSPLUS e2 = expr
    { JuraCompiler.jbinaryop JuraCompiler.Ops.Binary.opstringconcat e1 e2 }

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
| ELSE e = expr
    { ([],e) }
| WITH d = data THEN e = expr cs = cases
    { (((None,JuraCompiler.jcasevalue d),e)::(fst cs), snd cs) }
| WITH LET v = ident EQUAL d = data THEN e = expr cs = cases
    { (((Some v,JuraCompiler.jcasevalue d),e)::(fst cs), snd cs) }
| WITH AS brand = STRING THEN e = expr tcs = cases
    { (((None,JuraCompiler.jcasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }
| WITH LET v = ident AS brand = STRING THEN e = expr tcs = cases
    { (((Some v,JuraCompiler.jcasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }

(* New struct *)
reclist:
| 
    { [] }
| a = att
    { [a] }
| a = att COMMA rl = reclist
    { a :: rl }

att:
| an = IDENT COLON e = expr
    { (Util.char_list_of_string an, e) }

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
    { JuraCompiler.Data.dfloat f }

(* ident *)
ident:
| i = IDENT
    { Util.char_list_of_string i }

(* identlist *)
identlist:
| i = IDENT
    { (Util.char_list_of_string i)::[] }
| i = IDENT COMMA il = identlist
    { (Util.char_list_of_string i)::il }

(* Safe identifier *)
safeident:
| i = safeident_base
    { Util.char_list_of_string i }

safeident_base:
| i = IDENT { i }
| NAMESPACE { "namespace" }
| IMPORT { "import" }
| DEFINE { "define" }
| FUNCTION { "function" }
| CONTRACT { "contract" }
| CONCEPT { "concept" }
| TRANSACTION { "transaction" }
| ENUM { "enum" }
| EXTENDS { "extends" }
| OVER { "over" }
| CLAUSE { "clause" }
| ENFORCE { "enforce" }
| IF { "if" }
| THEN { "then" }
| ELSE { "else" }
| LET { "let" }
| FOR { "for" }
| IN { "in" }
| WHERE { "where" }
| RETURN { "return" }
| THROW { "throw" }
| THROWS { "throws" }
| VARIABLE { "variable" }
| AS { "as" }
| NEW { "new" }
| MATCH { "match" }
| TYPEMATCH { "typematch" }
| WITH { "with" }
| OR { "or" }
| AND { "and" }
| NOT { "not" }
| FLATTEN { "flatten" }
| AVG { "avg" }
| SUM { "sum" }
| COUNT { "count" }
| MIN { "min" }
| MAX { "max" }
| NIL { "nil" }
| TRUE { "true" }
| FALSE { "false" }

