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
open LexUtil
open ErgoUtil
open ErgoComp

let qname_of_qname_base qn =  
  begin match qn with
  | (None,last) -> (None,Util.char_list_of_string last)
  | (Some prefix, last) ->
      (Some (Util.char_list_of_string prefix),
       Util.char_list_of_string last)
  end

let relative_ref_of_qname_base qn =
  let (prefix,localname) = qname_of_qname_base qn in
  RelativeRef (prefix,localname)
%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token NAMESPACE IMPORT DEFINE FUNCTION
%token CONCEPT TRANSACTION ENUM EXTENDS
%token CONTRACT OVER CLAUSE
%token THROWS EMITS

%token ENFORCE IF THEN ELSE
%token LET FOREACH IN WHERE
%token RETURN THROW STATE
%token CONSTANT
%token NEW
%token MATCH WITH
%token SET EMIT

%token OR AND NOT

%token NIL
%token TRUE FALSE

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS MINUS STAR SLASH CARROT
%token PLUSI MINUSI STARI SLASHI
%token PLUSPLUS
%token DOT QUESTIONDOT COMMA COLON SEMI
%token QUESTION QUESTIONQUESTION UNDERSCORE
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
%left QUESTIONQUESTION
%left PLUS MINUS PLUSI MINUSI
%left STAR SLASH STARI SLASHI
%left CARROT
%left PLUSPLUS
%right NOT
%left DOT QUESTIONDOT

%start <ErgoComp.ErgoCompiler.ergo_module> main

%%

main:
| p = emodule EOF
    { p }


emodule:
| NAMESPACE qn = qname_prefix ims = imports ss = decls
    { { module_namespace = Util.char_list_of_string qn;
        module_imports = ims;
        module_declarations = ss; } }

imports:
|   { [] }
| IMPORT qn = qname_prefix ims = imports
    { (ErgoUtil.cto_import_decl_of_import_namespace qn) :: ims }

    
decls:
|
    { [] }
| s = decl ss = decls
    { s :: ss }

decl:
| DEFINE CONCEPT cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (ErgoCompiler.mk_ergo_type_declaration cn (ErgoTypeConcept (oe,ctype))) }
| DEFINE TRANSACTION cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (ErgoCompiler.mk_ergo_type_declaration cn (ErgoTypeTransaction (oe,ctype))) }
| DEFINE ENUM cn = ident et = ergo_type_enum_decl
    { ErgoCompiler.dtype (ErgoCompiler.mk_ergo_type_declaration cn (ErgoTypeEnum et)) }
| DEFINE CONSTANT v = ident EQUAL e = expr
    { ErgoCompiler.dconstant v e }
| DEFINE FUNCTION cn = ident LPAREN RPAREN COLON out = paramtype mt = maythrow LCURLY fs = fstmt RCURLY
    { ErgoCompiler.dfunc
        { function_name = cn;
          function_lambda =
          { lambda_params = [];
            lambda_output = out;
            lambda_throws = fst mt;
            lambda_emits = snd mt;
            lambda_body = fs; } } }
| DEFINE FUNCTION cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY fs = fstmt RCURLY
    { ErgoCompiler.dfunc
        { function_name = cn;
          function_lambda =
          { lambda_params = ps;
            lambda_output = out;
            lambda_throws = fst mt;
            lambda_emits = snd mt;
            lambda_body = fs; } } }
| CONTRACT cn = ident OVER tn = paramtype ms = mayhavestate LCURLY ds = clauses RCURLY
    { ErgoCompiler.dcontract
        { contract_name = cn;
          contract_template = tn;
          contract_state = ms;
          contract_clauses = ds; } }
| s = stmt SEMI
    { ErgoCompiler.dstmt s }

ergo_type_class_decl:
| LCURLY rt = rectype RCURLY
    { (None, rt) }
| EXTENDS qn = qname_base LCURLY rt = rectype RCURLY
    { (Some (relative_ref_of_qname_base qn), rt) }

ergo_type_enum_decl:
| LCURLY il = identlist RCURLY
    { il }

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
          lambda_throws = fst mt;
          lambda_emits = snd mt;
          lambda_body = e; } } }
| CLAUSE cn = ident LPAREN ps = params RPAREN COLON out = paramtype mt = maythrow LCURLY s = stmt RCURLY
    { { clause_name = cn;
        clause_lambda =
        { lambda_params = ps;
          lambda_output = out;
          lambda_throws = fst mt;
          lambda_emits = snd mt;
          lambda_body = s; } } }

maythrow:
|
  { (None,None) }
| THROWS tt = paramtype
  { (Some tt,None) }
| EMITS et = paramtype
  { (None,Some et) }
| THROWS tt = paramtype EMITS et = paramtype
  { (Some tt,Some et) }

mayhavestate:
|
  { None }
| STATE tt = paramtype
  { Some tt }

params:
| p = param
    { p :: [] }
| p = param COMMA ps = params
    { p :: ps }

param:
| pn = IDENT
    { (Util.char_list_of_string pn, ErgoCompiler.ergo_type_any) }
| pn = IDENT COLON pt = paramtype
    { (Util.char_list_of_string pn, pt) }

paramtype:
| qn = qname_base
    { begin match qn with
      | (None, "Boolean") -> ErgoCompiler.ergo_type_boolean
      | (None, "String") -> ErgoCompiler.ergo_type_string
      | (None, "Double") -> ErgoCompiler.ergo_type_double
      | (None, "Long") -> ErgoCompiler.ergo_type_long
      | (None, "Integer") -> ErgoCompiler.ergo_type_integer
      | (None, "DateTime") -> ErgoCompiler.ergo_type_dateTime
      | (None, "Empty") -> ErgoCompiler.ergo_type_none
      | (None, "Any") -> ErgoCompiler.ergo_type_any
      | _ ->
          ErgoCompiler.ergo_type_class_ref (relative_ref_of_qname_base qn)
      end }
| LCURLY rt = rectype RCURLY
    { ErgoCompiler.ergo_type_record rt }
| pt = paramtype LBRACKET RBRACKET
    { ErgoCompiler.ergo_type_array pt }
| pt = paramtype QUESTION
    { ErgoCompiler.ergo_type_option pt }

rectype:
| 
    { [] }
| at = attributetype
    { [at] }
| at = attributetype COMMA rt = rectype
    { at :: rt }

attributetype:
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
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { ErgoCompiler.scallclause (Util.char_list_of_string fn) el }
| LET v = ident EQUAL e1 = expr SEMI s2 = stmt
    { ErgoCompiler.slet v e1 s2 }
| LET v = ident COLON t = paramtype EQUAL e1 = expr SEMI s2 = stmt
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
    { raise (LexError ("Cannot throw inside a function, you have to be in a Clause")) }
| LET v = ident EQUAL e1 = expr SEMI s2 = fstmt
    { ErgoCompiler.slet v e1 s2 }
| LET v = ident COLON t = paramtype EQUAL e1 = expr SEMI s2 = fstmt
    { ErgoCompiler.slet_typed v t e1 s2 }
| IF e1 = expr THEN s2 = fstmt ELSE s3 = fstmt
    { ErgoCompiler.sif e1 s2 s3 }
| ENFORCE e1 = expr ELSE s2 = fstmt SEMI s3 = fstmt
    { raise (LexError ("Cannot use enforce inside a function, you have to be in a Clause")) }
| ENFORCE e1 = expr SEMI s3 = fstmt
    { raise (LexError ("Cannot use enforce inside a function, you have to be in a Clause")) }
| SET STATE e1 = expr SEMI s2 = fstmt
    { raise (LexError ("Cannot set state inside a function, you have to be in a Clause")) }
| EMIT e1 = expr SEMI s2 = fstmt
    { raise (LexError ("Cannot emit inside a function, you have to be in a Clause")) }
| MATCH e0 = expr csd = cases_fstmt
    { ErgoCompiler.smatch e0 (fst csd) (snd csd) }

(* cases *)
type_annotation:
| (* Empty *)
    { None }
| COLON tn = IDENT
    { Some (Util.char_list_of_string tn) }

cases_stmt:
| ELSE s = stmt
    { ([],s) }
| WITH d = data THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecasedata d,s)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecaselet v ta,s)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = stmt cs = cases_stmt
    { ((ErgoCompiler.ecasewildcard ta,e)::(fst cs), snd cs) }
| WITH LET v = ident QUESTION ta = type_annotation THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecaseletoption v ta,s)::(fst cs), snd cs) }

cases_fstmt:
| ELSE s = fstmt
    { ([],s) }
| WITH d = data THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecasedata d,s)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecaselet v ta,s)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecasewildcard ta,e)::(fst cs), snd cs) }
| WITH LET v = ident QUESTION ta = type_annotation THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecaseletoption v ta ,s)::(fst cs), snd cs) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Call *)
| fn = IDENT LPAREN el = exprlist RPAREN
    { ErgoCompiler.ecallfun (Util.char_list_of_string fn) el }
(* Constants *)
| NIL
    { ErgoCompiler.econst ErgoCompiler.ErgoData.dunit }
| TRUE
    { ErgoCompiler.econst (ErgoCompiler.ErgoData.dbool true) }
| FALSE
    { ErgoCompiler.econst (ErgoCompiler.ErgoData.dbool false) }
| i = INT
    { ErgoCompiler.econst (ErgoCompiler.ErgoData.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { ErgoCompiler.econst (ErgoCompiler.ErgoData.dfloat f) }
| s = STRING
    { ErgoCompiler.econst (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s)) }
| LBRACKET el = exprlist RBRACKET
    { ErgoCompiler.earray el }
(* Expressions *)
| v = IDENT
    { ErgoCompiler.evar (Util.char_list_of_string v) }
| e = expr DOT a = safeident
    { ErgoCompiler.edot a e }
| e = expr QUESTIONDOT a = safeident
    { ErgoCompiler.eoptionaldot a e }
| e1 = expr QUESTIONQUESTION e2 = expr
    { ErgoCompiler.eoptionaldefault e1 e2 }
| IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { ErgoCompiler.eif e1 e2 e3 }
| NEW qn = qname LCURLY r = reclist RCURLY
    { ErgoCompiler.enew (ErgoCompiler.mk_relative_ref (fst qn) (snd qn)) r }
| LCURLY r = reclist RCURLY
    { ErgoCompiler.erecord r }
| CONTRACT
    { ErgoCompiler.ethis_contract }
| CLAUSE
    { ErgoCompiler.ethis_clause }
| STATE
    { ErgoCompiler.ethis_state }
| LET v = ident EQUAL e1 = expr SEMI e2 = expr
    { ErgoCompiler.elet v None e1 e2 }
| LET v = ident COLON t = paramtype EQUAL e1 = expr SEMI e2 = expr
    { ErgoCompiler.elet v (Some t) e1 e2 }
| MATCH e0 = expr csd = cases
    { ErgoCompiler.ematch e0 (fst csd) (snd csd) }
| FOREACH fl = foreachlist RETURN e2 = expr
    { ErgoCompiler.eforeach fl None e2 }
| FOREACH fl = foreachlist WHERE econd = expr RETURN e2 = expr
    { ErgoCompiler.eforeach fl (Some econd) e2 }
(* Unary operators *)
| NOT e = expr
    { ErgoCompiler.eunaryop ErgoCompiler.ErgoOps.Unary.opneg e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.ErgoOps.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.opequal e1 e2) }
| e1 = expr LT e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.oplt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.ople e1 e2 }
| e1 = expr GT e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.ErgoOps.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.ople e1 e2) }
| e1 = expr GTEQ e2 = expr
    { ErgoCompiler.eunaryop ErgoCompiler.ErgoOps.Unary.opneg (ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.oplt e1 e2) }
| e1 = expr MINUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Double.opminus e1 e2 }
| e1 = expr PLUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Double.opplus e1 e2 }
| e1 = expr STAR e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Double.opmult e1 e2 }
| e1 = expr SLASH e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Double.opdiv e1 e2 }
| e1 = expr CARROT e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Double.oppow e1 e2 }
| e1 = expr MINUSI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Integer.opminusi e1 e2 }
| e1 = expr PLUSI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Integer.opplusi e1 e2 }
| e1 = expr STARI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Integer.opmulti e1 e2 }
| e1 = expr SLASHI e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.Integer.opdivi e1 e2 }
| e1 = expr AND e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.opor e1 e2 }
| e1 = expr PLUSPLUS e2 = expr
    { ErgoCompiler.ebinaryop ErgoCompiler.ErgoOps.Binary.opstringconcat e1 e2 }

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
    { ((ErgoCompiler.ecasedata d,e)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = expr cs = cases
    { ((ErgoCompiler.ecasewildcard ta,e)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN e = expr cs = cases
    { ((ErgoCompiler.ecaselet v ta,e)::(fst cs), snd cs) }
| WITH LET v = ident QUESTION ta = type_annotation THEN e = expr tcs = cases
    { ((ErgoCompiler.ecaseletoption v ta,e)::(fst tcs), snd tcs) }

(* New struct *)
reclist:
| 
    { [] }
| a = attribute
    { [a] }
| a = attribute COMMA rl = reclist
    { a :: rl }

attribute:
| an = safeident COLON e = expr
    { (an, e) }

(* Qualified name *)
qname_base:
| STAR
    { (None,"*") }
| i = safeident_base
    { (None,i) }
| i = safeident_base DOT q = qname_base
    { if i = "*"
      then raise (LexError "'*' can only be last in a qualified name")
      else
        begin match q with
  | (None, last) -> (Some i, last)
  | (Some prefix, last) -> (Some (i ^ "." ^ prefix), last)
  end }

qname:
| qn = qname_base
    { qname_of_qname_base qn }

qname_prefix:
| qn = qname_base
    { begin match qn with
      | (None,last) -> last
      | (Some prefix, last) -> prefix ^ "." ^ last
      end }

(* data *)
data:
| s = STRING
    { ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s) }
| i = INT
    { ErgoCompiler.ErgoData.dnat i }
| f = FLOAT
    { ErgoCompiler.ErgoData.dfloat f }

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
| CONCEPT { "concept" }
| TRANSACTION { "transaction" }
| ENUM { "enum" }
| EXTENDS { "extends" }
| CONTRACT { "contract" }
| OVER { "over" }
| CLAUSE { "clause" }
| THROWS { "throws" }
| EMITS { "emits" }
| STATE { "state" }
| ENFORCE { "enforce" }
| IF { "if" }
| THEN { "then" }
| ELSE { "else" }
| LET { "let" }
| FOREACH { "foreach" }
| RETURN { "return" }
| IN { "in" }
| WHERE { "where" }
| THROW { "throw" }
| NEW { "new" }
| CONSTANT { "constant" }
| MATCH { "match" }
| SET { "set" }
| EMIT { "emit" }
| WITH { "with" }
| OR { "or" }
| AND { "and" }
| NIL { "nil" }
| TRUE { "true" }
| FALSE { "false" }

