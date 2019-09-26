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

(* File provenance *)
let mk_provenance
    (start_pos: Lexing.position)
    (end_pos: Lexing.position) : provenance =
    mk_provenance_of_loc_pair !filename start_pos end_pos

(* QNames *)
let relative_name_of_qname qn =
  begin match qn with
  | (None,last) -> (None,Util.char_list_of_string last)
  | (Some prefix, last) ->
      (Some (Util.char_list_of_string prefix),
       Util.char_list_of_string last)
  end

let make_template_input prov =
  ErgoCompiler.ethis_this prov

let make_template_variable prov v =
  ErgoCompiler.ecallfun
    prov
    (relative_name_of_qname (Some "org.accordproject.ergo.stdlib","toText"))
    [ErgoCompiler.eunaryoperator prov
       (EOpDot (Util.char_list_of_string v))
       (make_template_input prov)]

let make_template_computed prov e =
  ErgoCompiler.ecallfun
    prov
    (relative_name_of_qname (Some "org.accordproject.ergo.stdlib","toText"))
    [e]

let make_template_variable_as prov v s =
  ErgoCompiler.ecallfun prov
    (relative_name_of_qname (Some "org.accordproject.time","format"))
    [ErgoCompiler.eunaryoperator prov
       (EOpDot (Util.char_list_of_string v))
       (make_template_input prov);
     ErgoCompiler.econst prov
       (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s))]

(* Construct AST for variables *)
let wrap_template_variable prov name ve =
  let varparam =
    ErgoCompiler.econst prov
      (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string name))
  in
  ErgoCompiler.ecallfun
    prov
    (relative_name_of_qname (Some "org.accordproject.ergo.template","variableTag"))
    [varparam;ve]

let wrap_template_variable_as prov name ve fe =
  let varparam =
    ErgoCompiler.econst prov
      (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string name))
  in
  ErgoCompiler.ecallfun
    prov
    (relative_name_of_qname (Some "org.accordproject.ergo.template","variableTagAs"))
    [varparam;ve;fe]

let wrap_template_computed prov e =
  let textparam = e in
  ErgoCompiler.ecallfun
    prov
    (relative_name_of_qname (Some "org.accordproject.ergo.template","computedTag"))
    [textparam]

let make_template_list prov name ve =
  let a = Util.char_list_of_string name in
  let e = ErgoCompiler.eunaryoperator prov (EOpDot a) (ErgoCompiler.ethis_this prov) in
  let fl = (ErgoCompiler.this_name, e) :: [] in
  let bullet = make_list_sep () in
  ErgoCompiler.ebinarybuiltin prov
    ErgoCompiler.ErgoOps.Binary.opstringjoin
    (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string "")))
    (ErgoCompiler.eforeach prov fl None
       (ErgoCompiler.etext prov
          (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string bullet)) :: ve)))

let make_template_order prov name ve =
  let a = Util.char_list_of_string name in
  let e = ErgoCompiler.eunaryoperator prov (EOpDot a) (ErgoCompiler.ethis_this prov) in
  let fl = (ErgoCompiler.this_name, e) :: [] in
  let bullet = make_order_sep () in
  ErgoCompiler.ebinarybuiltin prov
    ErgoCompiler.ErgoOps.Binary.opstringjoin
    (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string "")))
    (ErgoCompiler.eforeach prov fl None
       (ErgoCompiler.etext prov
          (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string bullet)) :: ve)))

let make_template_join prov name sep ve =
  let a = Util.char_list_of_string name in
  let e = ErgoCompiler.eunaryoperator prov (EOpDot a) (ErgoCompiler.ethis_this prov) in
  let fl = (ErgoCompiler.this_name, e) :: [] in
  ErgoCompiler.ebinarybuiltin prov
    ErgoCompiler.ErgoOps.Binary.opstringjoin
    (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string sep)))
    (ErgoCompiler.eforeach prov fl None
       (ErgoCompiler.etext prov ve))

let make_template_with prov name ve =
  let a = Util.char_list_of_string name in
  let e = ErgoCompiler.eunaryoperator prov (EOpDot a) (ErgoCompiler.ethis_this prov) in
  ErgoCompiler.elet prov ErgoCompiler.this_name None e
    (ErgoCompiler.etext prov ve)

let make_template_clause prov name ve =
  make_template_with prov name ve (* XXX May have to be revised eventually *)

let make_template_if_else prov name ve1 ve2 =
  let a = Util.char_list_of_string name in
  let econd = ErgoCompiler.eunaryoperator prov (EOpDot a) (ErgoCompiler.ethis_this prov) in
  wrap_template_variable
    prov
    name
    (ErgoCompiler.eif prov
       econd
       (ErgoCompiler.etext prov ve1)
       (ErgoCompiler.etext prov ve2))

let make_template_if prov name ve1 =
  let ve2 = [ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string ""))] in
  make_template_if_else prov name ve1 ve2

%}

%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> IDENT

%token OPENTEXT
%token CLOSEEXPR
%token CLOSEVAR
%token <string> CLOSETEXT EOFTEXT
%token <string> OPENEXPR
%token <string> OPENVAR OPENVARSHARP OPENVARSLASH OPENVARELSE

%token NAMESPACE IMPORT DEFINE FUNCTION
%token ABSTRACT TRANSACTION CONCEPT EVENT ASSET PARTICIPANT ENUM EXTENDS
%token CONTRACT OVER CLAUSE
%token EMITS

%token ENFORCE IF THEN ELSE
%token LET INFO FOREACH IN WHERE
%token RETURN THROW STATE CALL SEND
%token CONSTANT
%token MATCH WITH
%token SET EMIT

%token OR AND NOT

%token UNIT NONE SOME
%token TRUE FALSE

%token EQUAL NEQUAL
%token LT GT LTEQ GTEQ
%token PLUS MINUS STAR SLASH PERCENT CARROT
%token PLUSPLUS
%token DOT QUESTIONDOT COMMA COLON SEMI
%token QUESTION QUESTIONQUESTION UNDERSCORE
%token TILDE
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LCURLY RCURLY
%token EOF

%token AS LIST ORDER JOIN OPTIONAL

%left SEMI
%left ELSE
%left RETURN
%left MATCH IF LET CONTRACT INFO
%left OR
%left AND
%left EQUAL NEQUAL
%left LT GT LTEQ GTEQ
%left QUESTIONQUESTION
%left PLUS MINUS
%left STAR SLASH PERCENT
%left CARROT
%left PLUSPLUS
%nonassoc uminus
%right NOT
%right LBRACKET
%left DOT QUESTIONDOT

%start <ErgoComp.ErgoCompiler.ergo_module> main_module
%start <ErgoComp.ErgoCompiler.ergo_declaration list> top_decls
%start <ErgoComp.ErgoCompiler.ergo_expr> template

%%

main_module:
| p = emodule EOF
    { p }

top_decls:
| EOF
    { [] }
| d = top_decl dl = top_decls
    { d :: dl }

emodule:
| NAMESPACE qn = qname_prefix ds = decls
    { { module_annot = mk_provenance $startpos $endpos;
        module_file = Util.char_list_of_string !filename;
        module_prefix = Util.char_list_of_string (Util.class_prefix_of_filename !filename);
        module_namespace = qn;
        module_declarations = ds; } }

decls:
|
    { [] }
| d = decl dl = decls
    { d :: dl }

top_decl:
| d = decl
    { d }
| NAMESPACE qn = qname_prefix
    { ErgoCompiler.dnamespace
        (mk_provenance $startpos $endpos)
        qn }
| SET CONTRACT qn = qname OVER e = expr
    { ErgoCompiler.dsetcontract (mk_provenance $startpos $endpos) qn e }
| s = stmt
    { ErgoCompiler.dstmt (mk_provenance $startpos $endpos) s }

decl:
| IMPORT qn = qname_import
    { ErgoCompiler.dimport
        (mk_provenance $startpos $endpos)
        qn }
| DEFINE ma = maybe_abstract TRANSACTION cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeTransaction (ma,oe,ctype))) }
| DEFINE ma = maybe_abstract CONCEPT cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeConcept (ma,oe,ctype))) }
| DEFINE ma = maybe_abstract EVENT cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeEvent (ma,oe,ctype))) }
| DEFINE ma = maybe_abstract ASSET cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeAsset (ma,oe,ctype))) }
| DEFINE ma = maybe_abstract PARTICIPANT cn = ident dt = ergo_type_class_decl
    { let (oe,ctype) = dt in
      ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeParticipant (ma,oe,ctype))) }
| DEFINE ENUM cn = ident et = ergo_type_enum_decl
    { ErgoCompiler.dtype (mk_provenance $startpos $endpos)
        (ErgoCompiler.mk_ergo_type_declaration (mk_provenance $startpos $endpos) cn (ErgoTypeEnum et)) }
| DEFINE CONSTANT vt = identannot EQUAL e = expr
    { ErgoCompiler.dconstant (mk_provenance $startpos $endpos) (fst vt) (snd vt) e }
| DEFINE FUNCTION fn = ident LPAREN ps = params RPAREN out = outtype fb = fbody
    { ErgoCompiler.dfunc (mk_provenance $startpos $endpos) fn
        { function_annot = mk_provenance $startpos $endpos;
          function_sig =
          { type_signature_annot = (mk_provenance $startpos $endpos);
            type_signature_params = ps;
            type_signature_output = out;
            type_signature_emits = None };
          function_body = fb; } }
| CONTRACT cn = ident OVER tn = paramtype ms = mayhavestate LCURLY ds = clauses RCURLY
    { ErgoCompiler.dcontract (mk_provenance $startpos $endpos) cn
        { contract_annot = mk_provenance $startpos $endpos;
          contract_template = tn;
          contract_state = ms;
          contract_clauses = ds; } }

fbody:
|
    { None }
| LCURLY fs = fstmt RCURLY
    { Some fs }


maybe_abstract:
|
    { false }
| ABSTRACT
    { true }

ergo_type_class_decl:
| LCURLY rt = rectype RCURLY
    { (None, rt) }
| EXTENDS qn = qname LCURLY rt = rectype RCURLY
    { (Some qn, rt) }

ergo_type_enum_decl:
| LCURLY il = identlist RCURLY
    { il }

clauses:
| 
    { [] }
| c = clause cl = clauses
    { c :: cl }

clause:
(* | CLAUSE cn = ident LPAREN ps = params RPAREN out = outtype et = emittypes LCURLY s = stmt RCURLY -- XXX Force explicit declaration of output for now due to Cicero target bug *)
| CLAUSE cn = ident LPAREN ps = params RPAREN COLON out = paramtype et = emittypes LCURLY s = stmt RCURLY
    { { clause_annot = mk_provenance $startpos $endpos;
        clause_name = cn;
        clause_sig =
        { type_signature_annot = (mk_provenance $startpos $endpos);
          type_signature_params = ps;
          type_signature_output = Some out;
          type_signature_emits = et };
        clause_body = Some s; } }

outtype:
|
  { None }
| COLON out = paramtype
  { Some out }

emittypes:
|
  { None }
| EMITS et = paramtype
  { Some et }

mayhavestate:
|
  { None }
| STATE tt = paramtype
  { Some tt }

params:
| 
    { [] }
| p = param
    { p :: [] }
| p = param COMMA ps = params
    { p :: ps }

param:
| pn = IDENT
    { (Util.char_list_of_string pn, ErgoCompiler.ergo_type_any (mk_provenance $startpos $endpos)) }
| pn = IDENT COLON pt = paramtype
    { (Util.char_list_of_string pn, pt) }

paramtype:
| tn = tname
    { tn }
| LCURLY rt = rectype RCURLY
    { ErgoCompiler.ergo_type_record (mk_provenance $startpos $endpos) rt }
| pt = paramtype LBRACKET RBRACKET
    { ErgoCompiler.ergo_type_array (mk_provenance $startpos $endpos) pt }
| pt = paramtype QUESTION
    { ErgoCompiler.ergo_type_option (mk_provenance $startpos $endpos) pt }

rectype:
| 
    { [] }
| at = attributetype
    { [at] }
| at = attributetype COMMA rt = rectype
    { at :: rt }

attributetype:
| a = safeident COLON pt = paramtype
    { (a, pt) }

stmt:
(* Statments *)
| RETURN
    { ErgoCompiler.sreturnempty (mk_provenance $startpos $endpos) }
| RETURN e1 = expr
    { ErgoCompiler.sreturn (mk_provenance $startpos $endpos) e1 }
| THROW e1 = expr
    { ErgoCompiler.sthrow (mk_provenance $startpos $endpos) e1 }
(* Call *)
| CALL cln = IDENT LPAREN el = exprlist RPAREN
    { let e0 = ErgoCompiler.ethis_contract (mk_provenance $startpos $endpos) in
      ErgoCompiler.scallclause (mk_provenance $startpos $endpos) e0 (Util.char_list_of_string cln) el }
| SEND e1 = expr
    { let e0 = ErgoCompiler.ethis_contract (mk_provenance $startpos $endpos) in
      ErgoCompiler.scallcontract (mk_provenance $startpos $endpos) e0 e1 }
| LET vt = identannot EQUAL e1 = expr SEMI s2 = stmt
    { ErgoCompiler.slet (mk_provenance $startpos $endpos) (fst vt) (snd vt) e1 s2 }
| INFO LPAREN e1 = expr RPAREN SEMI s2 = stmt
    { ErgoCompiler.sprint (mk_provenance $startpos $endpos) e1 s2 }
| IF e1 = expr THEN s2 = stmt ELSE s3 = stmt
    { ErgoCompiler.sif (mk_provenance $startpos $endpos) e1 s2 s3 }
| ENFORCE e1 = expr ELSE s2 = stmt SEMI s3 = stmt
    { ErgoCompiler.senforce (mk_provenance $startpos $endpos) e1 (Some s2) s3 }
| ENFORCE e1 = expr SEMI s3 = stmt
    { ErgoCompiler.senforce (mk_provenance $startpos $endpos) e1 None s3 }
| SET STATE e1 = expr SEMI s2 = stmt
    { ErgoCompiler.ssetstate (mk_provenance $startpos $endpos) e1 s2 }
| EMIT e1 = expr SEMI s2 = stmt
    { ErgoCompiler.semit (mk_provenance $startpos $endpos) e1 s2 }
| MATCH e0 = expr csd = cases_stmt
    { ErgoCompiler.smatch (mk_provenance $startpos $endpos) e0 (fst csd) (snd csd) }

fstmt:
(* Statments *)
| RETURN
    { ErgoCompiler.efunreturnempty (mk_provenance $startpos $endpos) }
| RETURN e1 = expr
    { ErgoCompiler.efunreturn (mk_provenance $startpos $endpos) e1 }
| THROW e1 = expr
    { raise (LexError ("Cannot throw inside a function, you have to be in a Clause")) }
| LET vt = identannot EQUAL e1 = expr SEMI s2 = fstmt
    { ErgoCompiler.elet (mk_provenance $startpos $endpos) (fst vt) (snd vt) e1 s2 }
| IF e1 = expr THEN s2 = fstmt ELSE s3 = fstmt
    { ErgoCompiler.eif (mk_provenance $startpos $endpos) e1 s2 s3 }
| ENFORCE e1 = expr ELSE s2 = fstmt SEMI s3 = fstmt
    { raise (LexError ("Cannot use enforce inside a function, you have to be in a Clause")) }
| ENFORCE e1 = expr SEMI s3 = fstmt
    { raise (LexError ("Cannot use enforce inside a function, you have to be in a Clause")) }
| SET STATE e1 = expr SEMI s2 = fstmt
    { raise (LexError ("Cannot set state inside a function, you have to be in a Clause")) }
| EMIT e1 = expr SEMI s2 = fstmt
    { raise (LexError ("Cannot emit inside a function, you have to be in a Clause")) }
| MATCH e0 = expr csd = cases_fstmt
    { ErgoCompiler.ematch (mk_provenance $startpos $endpos) e0 (fst csd) (snd csd) }

(* cases *)
type_annotation:
| (* Empty *)
    { None }
| COLON qn = qname
    { Some qn }

cases_stmt:
| ELSE s = stmt
    { ([],s) }
| WITH v = qname THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecaseenum (mk_provenance $startpos $endpos) v,s)::(fst cs), snd cs) }
| WITH d = data THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecasedata (mk_provenance $startpos $endpos) d,s)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = stmt cs = cases_stmt
    { ((ErgoCompiler.ecasewildcard (mk_provenance $startpos $endpos) ta,e)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecaselet (mk_provenance $startpos $endpos) v ta,s)::(fst cs), snd cs) }
| WITH LET QUESTION v = ident ta = type_annotation THEN s = stmt cs = cases_stmt
    { ((ErgoCompiler.ecaseletoption (mk_provenance $startpos $endpos) v ta,s)::(fst cs), snd cs) }

cases_fstmt:
| ELSE s = fstmt
    { ([],s) }
| WITH v = qname THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecaseenum (mk_provenance $startpos $endpos) v,s)::(fst cs), snd cs) }
| WITH d = data THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecasedata (mk_provenance $startpos $endpos) d,s)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecasewildcard (mk_provenance $startpos $endpos) ta,e)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecaselet (mk_provenance $startpos $endpos) v ta,s)::(fst cs), snd cs) }
| WITH LET QUESTION v = ident ta = type_annotation THEN s = fstmt cs = cases_fstmt
    { ((ErgoCompiler.ecaseletoption (mk_provenance $startpos $endpos) v ta ,s)::(fst cs), snd cs) }

expr:
(* Parenthesized expression *)
| LPAREN e = expr RPAREN
    { e }
(* Call *)
| fn = qname LPAREN el = exprlist RPAREN
    { ErgoCompiler.ecallfun (mk_provenance $startpos $endpos) fn el }
(* Constants *)
| UNIT
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) ErgoCompiler.ErgoData.dunit }
| NONE
    { ErgoCompiler.enone (mk_provenance $startpos $endpos) }
| SOME LPAREN e = expr RPAREN
    { ErgoCompiler.esome (mk_provenance $startpos $endpos) e }
| TRUE
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dbool true) }
| FALSE
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dbool false) }
| i = INT
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dnat (Util.coq_Z_of_int i)) }
| f = FLOAT
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dfloat f) }
| s = STRING
    { ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s)) }
| LBRACKET el = exprlist RBRACKET
    { ErgoCompiler.earray (mk_provenance $startpos $endpos) el }
(* Text *)
| OPENTEXT sl = textlist s0 = CLOSETEXT
    { let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
      let sl' = sl @ [slast] in
      ErgoCompiler.etext (mk_provenance $startpos $endpos) sl' }
(* Expressions *)
| v = qname
    { ErgoCompiler.evar (mk_provenance $startpos $endpos) v }
| e = expr DOT a = safeident
    { ErgoCompiler.eunaryoperator (mk_provenance $startpos $endpos) (EOpDot a) e }
| e = expr QUESTIONDOT a = safeident
    { ErgoCompiler.eoptionaldot (mk_provenance $startpos $endpos) a e }
| e1 = expr QUESTIONQUESTION e2 = expr
    { ErgoCompiler.eoptionaldefault (mk_provenance $startpos $endpos) e1 e2 }
| IF e1 = expr THEN e2 = expr ELSE e3 = expr
    { ErgoCompiler.eif (mk_provenance $startpos $endpos) e1 e2 e3 }
| qn = qname LCURLY r = reclist RCURLY
    { ErgoCompiler.enew (mk_provenance $startpos $endpos) qn r }
| LCURLY r = reclist RCURLY
    { ErgoCompiler.erecord (mk_provenance $startpos $endpos) r }
| CONTRACT
    { ErgoCompiler.ethis_contract (mk_provenance $startpos $endpos) }
| CLAUSE
    { ErgoCompiler.ethis_clause (mk_provenance $startpos $endpos) }
| STATE
    { ErgoCompiler.ethis_state (mk_provenance $startpos $endpos) }
| LET vt = identannot EQUAL e1 = expr SEMI e2 = expr
    { ErgoCompiler.elet (mk_provenance $startpos $endpos) (fst vt) (snd vt) e1 e2 }
| INFO LPAREN e1 = expr RPAREN SEMI e2 = expr
    { ErgoCompiler.eprint (mk_provenance $startpos $endpos) e1 e2 }
| MATCH e0 = expr csd = cases
    { ErgoCompiler.ematch (mk_provenance $startpos $endpos) e0 (fst csd) (snd csd) }
| FOREACH fl = foreachlist RETURN e2 = expr
    { ErgoCompiler.eforeach (mk_provenance $startpos $endpos) fl None e2 }
| FOREACH fl = foreachlist WHERE econd = expr RETURN e2 = expr
    { ErgoCompiler.eforeach (mk_provenance $startpos $endpos) fl (Some econd) e2 }
(* Array index *)
| e1 = expr LBRACKET e2 = expr RBRACKET
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opnth e1 e2 }
(* Unary operators *)
| MINUS e = expr %prec uminus
    { ErgoCompiler.eunaryoperator (mk_provenance $startpos $endpos) EOpUMinus e }
| NOT e = expr
    { ErgoCompiler.eunarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Unary.opneg e }
(* Binary operators *)
| e1 = expr EQUAL e2 = expr
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opequal e1 e2 }
| e1 = expr NEQUAL e2 = expr
    { ErgoCompiler.eunarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Unary.opneg (ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opequal e1 e2) }
| e1 = expr LT e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpLt e1 e2 }
| e1 = expr LTEQ e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpLe e1 e2 }
| e1 = expr GT e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpGt e1 e2 }
| e1 = expr GTEQ e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpGe e1 e2 }
| e1 = expr MINUS e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpMinus e1 e2 }
| e1 = expr PLUS e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpPlus e1 e2 }
| e1 = expr STAR e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpMultiply e1 e2 }
| e1 = expr SLASH e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpDivide e1 e2 }
| e1 = expr PERCENT e2 = expr
    { ErgoCompiler.ebinaryoperator (mk_provenance $startpos $endpos) EOpRemainder e1 e2 }
| e1 = expr CARROT e2 = expr
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.Double.oppow e1 e2 }
| e1 = expr AND e2 = expr
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opand e1 e2 }
| e1 = expr OR e2 = expr
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opor e1 e2 }
| e1 = expr PLUSPLUS e2 = expr
    { ErgoCompiler.ebinarybuiltin (mk_provenance $startpos $endpos) ErgoCompiler.ErgoOps.Binary.opstringconcat e1 e2 }

(* text *)
template:
| sl = textlist s0 = EOFTEXT
    { let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
      let sl' = sl @ [slast] in
      ErgoCompiler.etext (mk_provenance $startpos $endpos) sl' }

textlist:
|
    { [] }
| s0 = OPENEXPR e = expr CLOSEEXPR sl = textlist
    { let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
      sfirst :: (wrap_template_computed (mk_provenance $startpos $endpos) (make_template_computed (mk_provenance $startpos $endpos) e)) :: sl }
| s0 = OPENVAR ve = varexpr CLOSEVAR sl = textlist
    { let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
      sfirst :: ve :: sl }
| s0 = OPENVARSHARP CLAUSE v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARSLASH CLAUSE CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_clause (mk_provenance $startpos $endpos) v0 (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP LIST v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARSLASH LIST CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_list (mk_provenance $startpos $endpos) v0 (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP ORDER v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARSLASH ORDER CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_order (mk_provenance $startpos $endpos) v0 (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP JOIN v0 = safeblock_base sep = STRING CLOSEVAR sl1 = textlist s1 = OPENVARSLASH JOIN CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_join (mk_provenance $startpos $endpos) v0 sep (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP WITH v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARSLASH WITH CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_with (mk_provenance $startpos $endpos) v0 (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP IF v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARSLASH IF CLOSEVAR sl2 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        [sfirst] @ [make_template_if (mk_provenance $startpos $endpos) v0 (sl1 @ [slast])] @ sl2
      end }
| s0 = OPENVARSHARP IF v0 = safeblock_base CLOSEVAR sl1 = textlist s1 = OPENVARELSE CLOSEVAR sl2 = textlist s2 = OPENVARSLASH IF CLOSEVAR sl3 = textlist
    { begin
        let sfirst = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s0)) in
        let smid = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s1)) in
        let slast = ErgoCompiler.econst (mk_provenance $startpos $endpos) (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s2)) in
        [sfirst] @ [make_template_if_else (mk_provenance $startpos $endpos) v0 (sl1 @ [smid]) (sl2 @ [slast])] @ sl3
      end }

varexpr:
| v = IDENT AS s = STRING
    { let prov = mk_provenance $startpos $endpos in
      let ve = make_template_variable_as prov v s in
      wrap_template_variable_as prov v ve
        (ErgoCompiler.econst prov (ErgoCompiler.ErgoData.dstring (Util.char_list_of_string s))) }
| v = IDENT
    { let prov = mk_provenance $startpos $endpos in
      let ve = make_template_variable prov v in
      wrap_template_variable prov v ve }

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
    { ((ErgoCompiler.ecasedata (mk_provenance $startpos $endpos) d,e)::(fst cs), snd cs) }
| WITH v = qname THEN e = expr cs = cases
    { ((ErgoCompiler.ecaseenum (mk_provenance $startpos $endpos) v,e)::(fst cs), snd cs) }
| WITH UNDERSCORE ta = type_annotation THEN e = expr cs = cases
    { ((ErgoCompiler.ecasewildcard (mk_provenance $startpos $endpos) ta,e)::(fst cs), snd cs) }
| WITH LET v = ident ta = type_annotation THEN e = expr cs = cases
    { ((ErgoCompiler.ecaselet (mk_provenance $startpos $endpos) v ta,e)::(fst cs), snd cs) }
| WITH LET QUESTION v = ident ta = type_annotation THEN e = expr tcs = cases
    { ((ErgoCompiler.ecaseletoption (mk_provenance $startpos $endpos) v ta,e)::(fst tcs), snd tcs) }

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
      then ergo_raise (ergo_parse_error "'*' can only be last in a qualified name" !filename $startpos $endpos)
      else
        begin match q with
  | (None, last) -> (Some i, last)
  | (Some prefix, last) -> (Some (i ^ "." ^ prefix), last)
  end }

qname:
| i = IDENT
    { relative_name_of_qname (None,i) }
| TILDE qnb = qname_base
    { relative_name_of_qname qnb }

tname:
| i = safeident_base
    { begin match i with
      | "Boolean" -> ErgoCompiler.ergo_type_boolean (mk_provenance $startpos $endpos)
      | "String" -> ErgoCompiler.ergo_type_string (mk_provenance $startpos $endpos)
      | "Double" -> ErgoCompiler.ergo_type_double (mk_provenance $startpos $endpos)
      | "Long" -> ErgoCompiler.ergo_type_long (mk_provenance $startpos $endpos)
      | "Integer" -> ErgoCompiler.ergo_type_integer (mk_provenance $startpos $endpos)
      | "DateTime" -> ErgoCompiler.ergo_type_dateTime (mk_provenance $startpos $endpos)
      | "InternalFormat" -> ErgoCompiler.ergo_type_dateTime_format (mk_provenance $startpos $endpos)
      | "InternalDuration" -> ErgoCompiler.ergo_type_duration (mk_provenance $startpos $endpos)
      | "InternalPeriod" -> ErgoCompiler.ergo_type_period (mk_provenance $startpos $endpos)
      | "Unit" -> ErgoCompiler.ergo_type_unit (mk_provenance $startpos $endpos)
      | "Nothing" -> ErgoCompiler.ergo_type_nothing (mk_provenance $startpos $endpos)
      | "Any" -> ErgoCompiler.ergo_type_any (mk_provenance $startpos $endpos)
      | _ ->
          ErgoCompiler.ergo_type_class_ref
            (mk_provenance $startpos $endpos)
            (relative_name_of_qname (None,i))
      end }
| TILDE qnb = qname_base
    { ErgoCompiler.ergo_type_class_ref
        (mk_provenance $startpos $endpos)
        (relative_name_of_qname qnb) }

qname_prefix:
| qn = qname_base
    { begin match qn with
      | (_,"*") -> ergo_raise (ergo_parse_error "Malformed namespace" !filename $startpos $endpos)
      | (None,last) -> Util.char_list_of_string last
      | (Some prefix, last) -> Util.char_list_of_string (prefix ^ "." ^ last)
      end }

qname_import:
| qn = qname_base
    { begin match qn with
      | (None,_) -> ergo_raise (ergo_parse_error "Malformed import" !filename $startpos $endpos)
      | (Some prefix, "*") ->
          ImportAll (mk_provenance $startpos $endpos,
                     Util.char_list_of_string prefix)
      | (Some prefix, last) ->
          ImportName (mk_provenance $startpos $endpos,
                      Util.char_list_of_string prefix,
                      Util.char_list_of_string last)
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
identannot:
| i = ident
    { (i, None) }
| i = ident COLON t = paramtype
    { (i, Some t) }

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
| ABSTRACT { "abstract" }
| TRANSACTION { "transaction" }
| CONCEPT { "concept" }
| EVENT { "event" }
| ASSET { "asset" }
| PARTICIPANT { "participant" }
| ENUM { "enum" }
| EXTENDS { "extends" }
| CONTRACT { "contract" }
| OVER { "over" }
| CLAUSE { "clause" }
| EMITS { "emits" }
| STATE { "state" }
| CALL { "call" }
| SEND { "send" }
| ENFORCE { "enforce" }
| IF { "if" }
| THEN { "then" }
| ELSE { "else" }
| LET { "let" }
| INFO { "info" }
| FOREACH { "foreach" }
| RETURN { "return" }
| IN { "in" }
| WHERE { "where" }
| THROW { "throw" }
| CONSTANT { "constant" }
| MATCH { "match" }
| SET { "set" }
| EMIT { "emit" }
| WITH { "with" }
| OR { "or" }
| AND { "and" }
| UNIT { "unit" }
| NONE { "none" }
| SOME { "some" }
| TRUE { "true" }
| FALSE { "false" }

safeblock_base:
| i = IDENT { i }
| CLAUSE { "clause" }
| IF { "if" }
| FOREACH { "foreach" }
| WITH { "with" }
| LIST { "list" }
| OPTIONAL { "optional" }


