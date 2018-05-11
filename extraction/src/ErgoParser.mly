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
  open ErgoComp
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token NAMESPACE IMPORT DEFINE FUNCTION
%token CONCEPT TRANSACTION ENUM EXTENDS
%token CONTRACT OVER CLAUSE THROWS

%token ENFORCE IF THEN ELSE
%token LET FOREACH IN WHERE
%token RETURN THROW STATE
%token VARIABLE AS
%token NEW
%token MATCH TYPEMATCH WITH
%token SET EMIT

%token OR AND NOT

%token NIL
%token TRUE FALSE
%token ANY EMPTY

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS MINUS STAR SLASH CARROT
%token PLUSI MINUSI STARI SLASHI
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
%left PLUS MINUS PLUSI MINUSI
%left STAR SLASH STARI SLASHI
%left CARROT
%left PLUSPLUS
%right NOT
%left DOT

%start <ErgoComp.ErgoCompiler.ergo_package> main

%%

main:
| p = package EOF
    { p }


package:
| NAMESPACE qn = qname_prefix ss = decls
    { { package_namespace = Util.char_list_of_string qn;
				package_declarations = ss; } }

decls:
|
    { [] }
| s = decl ss = decls
    { s :: ss }

decl:
| DEFINE CONCEPT cn = ident dt = cto_class_decl
    { let (oe,ctype) = dt in EType (ErgoCompiler.mk_cto_declaration cn (CTOConcept (oe,ctype))) }
| DEFINE TRANSACTION cn = ident dt = cto_class_decl
    { let (oe,ctype) = dt in EType (ErgoCompiler.mk_cto_declaration cn (CTOTransaction (oe,ctype))) }
| DEFINE ENUM cn = ident et = cto_enum_decl
    { EType (ErgoCompiler.mk_cto_declaration cn (CTOEnum et)) }
| DEFINE VARIABLE v = ident EQUAL e = expr
    { EGlobal (v, e) }
| DEFINE FUNCTION cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY fs = fstmt RCURLY
    { EFunc
  { function_name = cn;
    function_lambda =
    { lambda_params = [];
      lambda_output = out;
      lambda_throw = mt;
      lambda_body = fs; } } }
| DEFINE FUNCTION cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY fs = fstmt RCURLY
    { EFunc
  { function_name = cn;
    function_lambda =
    { lambda_params = ps;
      lambda_output = out;
      lambda_throw = mt;
      lambda_body = fs; } } }
| IMPORT qn = qname_prefix
    { EImport (ErgoUtil.cto_import_decl_of_import_namespace qn) }
| c = contract
    { EContract c }

cto_class_decl:
| LCURLY rt = rectype RCURLY
    { (None, rt) }
| EXTENDS en = ident LCURLY rt = rectype RCURLY
    { (Some en, rt) }

cto_enum_decl:
| LCURLY il = identlist RCURLY
    { il }

contract:
| CONTRACT cn = ident OVER tn = ident LCURLY ds = clauses RCURLY
    { { contract_name = cn;
        contract_template = tn;
        contract_clauses = ds; } }

clauses:
| 
    { [] }
| c = clause cl = clauses
    { c :: cl }

clause:
| CLAUSE cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY e = stmt RCURLY
    { { clause_name = cn;
				clause_lambda =
				{ lambda_params = [];
					lambda_output = out;
					lambda_throw = mt;
					lambda_body = e; } } }
| CLAUSE cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY s = stmt RCURLY
    { { clause_name = cn;
        clause_lambda =
        { lambda_params = ps;
          lambda_output = out;
          lambda_throw = mt;
          lambda_body = s; } } }

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
    { (Util.char_list_of_string pn, ErgoCompiler.cto_any) }
| pn = IDENT COLON pt = paramtype
    { (Util.char_list_of_string pn, pt) }

paramtype:
| EMPTY
		{ ErgoCompiler.cto_empty }
| ANY
		{ ErgoCompiler.cto_any }
| pt = IDENT
    { begin match pt with
      | "Boolean" -> ErgoCompiler.cto_boolean
      | "String" -> ErgoCompiler.cto_string
      | "Double" -> ErgoCompiler.cto_double
      | "Long" -> ErgoCompiler.cto_long
      | "Integer" -> ErgoCompiler.cto_integer
      | "DateTime" -> ErgoCompiler.cto_dateTime
      | _ -> ErgoCompiler.cto_class_ref (Util.char_list_of_string pt)
      end }
| LCURLY rt = rectype RCURLY
    { ErgoCompiler.cto_record rt }
| pt = paramtype LBRACKET RBRACKET
    { ErgoCompiler.cto_array pt }
| pt = paramtype QUESTION
    { ErgoCompiler.cto_option pt }

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

stmt:
(* Statments *)
| RETURN
		{ ErgoCompiler.sreturnempty }
| RETURN e1 = expr
		{ ErgoCompiler.sreturn e1 }
| THROW e1 = expr
    { ErgoCompiler.sthrow e1 }
| DEFINE VARIABLE v = ident EQUAL e1 = expr SEMI s2 = stmt
    { ErgoCompiler.slet v e1 s2 }
| DEFINE VARIABLE v = ident COLON t = paramtype EQUAL e1 = expr SEMI s2 = stmt
    { ErgoCompiler.slet_typed v t e1 s2 }
| IF e1 = expr THEN s2 = stmt ELSE s3 = stmt
    { ErgoCompiler.sif e1 s2 s3 }
| ENFORCE e1 = expr ELSE s2 = stmt SEMI s3 = stmt
    { ErgoCompiler.senforce e1 (Some s2) s3 }
| ENFORCE e1 = expr SEMI s3 = stmt
    { ErgoCompiler.senforce e1 None s3 }
| SET STATE e1 = expr SEMI s2 = stmt
    { ErgoCompiler.ssetstate e1 s2 }
| EMIT e1 = expr SEMI s2 = stmt
    { ErgoCompiler.semit e1 s2 }
| MATCH e0 = expr csd = cases_stmt
    { ErgoCompiler.smatch e0 (fst csd) (snd csd) }

fstmt:
(* Statments *)
| RETURN
		{ ErgoCompiler.sfunreturnempty }
| RETURN e1 = expr
		{ ErgoCompiler.sfunreturn e1 }
| THROW e1 = expr
    { raise (Ergo_Error ("Cannot throw inside a function, you have to be in a Clause")) }
| DEFINE VARIABLE v = ident EQUAL e1 = expr SEMI s2 = fstmt
    { ErgoCompiler.slet v e1 s2 }
| DEFINE VARIABLE v = ident COLON t = paramtype EQUAL e1 = expr SEMI s2 = fstmt
    { ErgoCompiler.slet_typed v t e1 s2 }
| IF e1 = expr THEN s2 = fstmt ELSE s3 = fstmt
    { ErgoCompiler.sif e1 s2 s3 }
| ENFORCE e1 = expr ELSE s2 = fstmt SEMI s3 = fstmt
    { raise (Ergo_Error ("Cannot use enforce inside a function, you have to be in a Clause")) }
| ENFORCE e1 = expr SEMI s3 = fstmt
    { raise (Ergo_Error ("Cannot use enforce inside a function, you have to be in a Clause")) }
| SET STATE e1 = expr SEMI s2 = fstmt
    { raise (Ergo_Error ("Cannot set state inside a function, you have to be in a Clause")) }
| EMIT e1 = expr SEMI s2 = fstmt
    { raise (Ergo_Error ("Cannot emit inside a function, you have to be in a Clause")) }
| MATCH e0 = expr csd = cases_fstmt
    { ErgoCompiler.smatch e0 (fst csd) (snd csd) }

(* cases *)
cases_stmt:
| ELSE s = stmt
    { ([],s) }
| WITH d = data THEN s = stmt cs = cases_stmt
    { (((None,ErgoCompiler.ecasevalue d),s)::(fst cs), snd cs) }
| WITH LET v = ident EQUAL d = data THEN s = stmt cs = cases_stmt
    { (((Some v,ErgoCompiler.ecasevalue d),s)::(fst cs), snd cs) }
| WITH AS brand = STRING THEN s = stmt tcs = cases_stmt
    { (((None,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),s)::(fst tcs), snd tcs) }
| WITH LET v = ident AS brand = STRING THEN s = stmt tcs = cases_stmt
    { (((Some v,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),s)::(fst tcs), snd tcs) }

cases_fstmt:
| ELSE s = fstmt
    { ([],s) }
| WITH d = data THEN s = fstmt cs = cases_fstmt
    { (((None,ErgoCompiler.ecasevalue d),s)::(fst cs), snd cs) }
| WITH LET v = ident EQUAL d = data THEN s = fstmt cs = cases_fstmt
    { (((Some v,ErgoCompiler.ecasevalue d),s)::(fst cs), snd cs) }
| WITH AS brand = STRING THEN s = fstmt tcs = cases_fstmt
    { (((None,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),s)::(fst tcs), snd tcs) }
| WITH LET v = ident AS brand = STRING THEN s = fstmt tcs = cases_fstmt
    { (((Some v,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),s)::(fst tcs), snd tcs) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { ErgoCompiler.ecall (Util.char_list_of_string fn) el }
(* Constants *)
| NIL
    { ErgoCompiler.econst ErgoCompiler.Data.dunit }
| TRUE
    { ErgoCompiler.econst (ErgoCompiler.Data.dbool true) }
| FALSE
    { ErgoCompiler.econst (ErgoCompiler.Data.dbool false) }
| i = INT
    { ErgoCompiler.econst (ErgoCompiler.Data.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { ErgoCompiler.econst (ErgoCompiler.Data.dfloat f) }
| s = STRING
    { ErgoCompiler.econst (ErgoCompiler.Data.dstring (Util.char_list_of_string s)) }
| LBRACKET el = exprlist RBRACKET
    { ErgoCompiler.earray el }
(* Expressions *)
| v = IDENT
    { ErgoCompiler.evar (Util.char_list_of_string v) }
| e = expr DOT a = safeident
    { ErgoCompiler.edot a e }
| IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { ErgoCompiler.eif e1 e2 e3 }
| NEW qn = qname LCURLY r = reclist RCURLY
    { ErgoCompiler.enew (fst qn) (snd qn) r }
| LCURLY r = reclist RCURLY
    { ErgoCompiler.erecord r }
| CONTRACT
    { ErgoCompiler.ethis_contract }
| CLAUSE
    { ErgoCompiler.ethis_clause }
| STATE
    { ErgoCompiler.ethis_state }
| LET v = ident EQUAL e1 = expr SEMI e2 = expr
    { ErgoCompiler.elet v e1 e2 }
| LET v = ident COLON t = paramtype EQUAL e1 = expr SEMI e2 = expr
    { ErgoCompiler.elet_typed v t e1 e2 }
| MATCH e0 = expr csd = cases
    { ErgoCompiler.ematch e0 (fst csd) (snd csd) }
| FOREACH fl = foreachlist RETURN e2 = expr
    { ErgoCompiler.eforeach fl None e2 }
| FOREACH fl = foreachlist WHERE econd = expr RETURN e2 = expr
    { ErgoCompiler.eforeach fl (Some econd) e2 }
(* Unary operators *)
| NOT e = expr
    { ErgoCompiler.eunaryop ErgoCompiler.Ops.Unary.opneg e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.Ops.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.opequal e1 e2) }
| e1 = expr LT e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.oplt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.ople e1 e2 }
| e1 = expr GT e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.Ops.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.ople e1 e2) }
| e1 = expr GTEQ e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.Ops.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.oplt e1 e2) }
| e1 = expr MINUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Double.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Double.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Double.opmult e1 e2 }
| e1 = expr SLASH e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Double.opdiv e1 e2 }
| e1 = expr CARROT e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Double.oppow e1 e2 }
| e1 = expr MINUSI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Integer.opminusi e1 e2 }
| e1 = expr PLUSI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Integer.opplusi e1 e2 }
| e1 = expr STARI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Integer.opmulti e1 e2 }
| e1 = expr SLASHI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.Integer.opdivi e1 e2 }
| e1 = expr AND e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.opor e1 e2 }
| e1 = expr PLUSPLUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.Ops.Binary.opstringconcat e1 e2 }

(* foreach list *)
foreachlist:
| v = ident IN e = expr
    { (v,e) :: [] }
| v = ident IN e = expr COMMA fl = foreachlist
    { (v,e) :: fl }
| v = ident IN e = expr FOREACH fl = foreachlist
    { (v,e) :: fl }


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
    { (((None,ErgoCompiler.ecasevalue d),e)::(fst cs), snd cs) }
| WITH LET v = ident EQUAL d = data THEN e = expr cs = cases
    { (((Some v,ErgoCompiler.ecasevalue d),e)::(fst cs), snd cs) }
| WITH AS brand = STRING THEN e = expr tcs = cases
    { (((None,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }
| WITH LET v = ident AS brand = STRING THEN e = expr tcs = cases
    { (((Some v,ErgoCompiler.ecasetype (Util.char_list_of_string brand)),e)::(fst tcs), snd tcs) }

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
      then raise (Ergo_Error "'*' can only be last in a qualified name")
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
      | (None,last) -> last
      | (Some prefix, last) -> prefix ^ "." ^ last
      end }

(* data *)
data:
| s = STRING
    { ErgoCompiler.Data.dstring (Util.char_list_of_string s) }
| i = INT
    { ErgoCompiler.Data.dnat i }
| f = FLOAT
    { ErgoCompiler.Data.dfloat f }

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
| FOREACH { "foreach" }
| IN { "in" }
| WHERE { "where" }
| RETURN { "return" }
| THROW { "throw" }
| THROWS { "throws" }
| STATE { "state" }
| SET { "set" }
| EMIT { "emit" }
| VARIABLE { "variable" }
| AS { "as" }
| NEW { "new" }
| MATCH { "match" }
| TYPEMATCH { "typematch" }
| WITH { "with" }
| OR { "or" }
| AND { "and" }
| NIL { "nil" }
| TRUE { "true" }
| FALSE { "false" }

