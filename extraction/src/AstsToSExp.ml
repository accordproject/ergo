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

(* This module contains parsing utilities *)

open Util
open SExp

open JComp
open JuraCompiler

(****************
 * AST <-> SExp *
 ****************)

let coq_string_to_sstring (cl:char list) : sexp =
  SString (string_of_char_list cl)
let dbrands_to_sexp (bs:(char list) list) : sexp list =
  List.map coq_string_to_sstring bs
let coq_string_list_to_sstring_list = dbrands_to_sexp

let coq_sort_desc_to_sstring x =
  begin match x with
  | Ascending -> SString "asc"
  | Descending -> SString "desc"
  end
let coq_string_list_to_sstring_list_with_order l =
  List.concat (List.map (fun x -> [coq_string_to_sstring (fst x);coq_sort_desc_to_sstring (snd x)]) l)

let sstring_to_coq_string (se:sexp) : char list =
  begin match se with
  | SString s -> char_list_of_string s
  | _ -> raise (Jura_Error "Not well-formed S-expr for Coq string")
  end
let sexp_to_dbrands (bs:sexp list) : (char list) list =
  List.map sstring_to_coq_string bs
let sstring_list_to_coq_string_list = sexp_to_dbrands
let rec sstring_list_with_order_to_coq_string_list sl =
  begin match sl with
  | [] -> []
  | SString att :: SString "asc" :: sl' -> (char_list_of_string att, Ascending) :: (sstring_list_with_order_to_coq_string_list sl')
  | SString att :: SString "desc" :: sl' -> (char_list_of_string att, Descending) :: (sstring_list_with_order_to_coq_string_list sl')
  | _ -> raise (Jura_Error "Not well-formed S-expr for Coq orderBy")
  end

(* Data Section *)

let foreign_data_to_sexp (fd:enhanced_data) : sexp =
  match fd with
  | Enhancedfloat f -> SFloat f
  | Enhancedstring s -> STerm ("enhanced_string", (SString s)::[])
  | Enhancedtimescale ts -> STerm ("dtime_scale", (SString (PrettyCommon.timescale_as_string ts))::[])
  | Enhancedtimeduration td -> raise Not_found
  | Enhancedtimepoint tp -> raise Not_found
  | Enhancedsqldate td -> raise Not_found
  | Enhancedsqldateinterval tp -> raise Not_found

let rec data_to_sexp (d : Data.qdata) : sexp =
  match d with
  | Dunit -> STerm ("dunit", [])
  | Dnat n -> SInt n
  | Dbool b -> SBool b
  | Dstring s -> SString (string_of_char_list s)
  | Dcoll dl -> STerm ("dcoll", List.map data_to_sexp dl)
  | Drec adl -> STerm ("drec", List.map drec_to_sexp adl)
  | Dleft d -> STerm ("dleft", data_to_sexp d :: [])
  | Dright d -> STerm ("dright", data_to_sexp d :: [])
  | Dbrand (bs,d) -> STerm ("dbrand", (STerm ("brands", dbrands_to_sexp bs)) :: (STerm ("value", (data_to_sexp d) :: [])) :: [])
  | Dforeign fdt -> foreign_data_to_sexp (Obj.magic fdt)
and drec_to_sexp (ad : char list * Data.qdata) : sexp =
  STerm ("datt", (SString (string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : Data.qdata =
  match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SFloat f -> (Dforeign (Obj.magic (Enhancedfloat f)))
  | SString s -> Dstring (char_list_of_string s)
  | STerm ("dcoll", sel) ->
      Dcoll (List.map sexp_to_data sel)
  | STerm ("drec", asel) ->
      Drec (List.map sexp_to_drec asel)
  | STerm ("dleft", se' :: []) ->
      Dleft (sexp_to_data se')
  | STerm ("dright", se' :: []) ->
      Dright (sexp_to_data se')
  | STerm ("dbrand", (STerm ("brands", bs)) :: (STerm ("value", se' :: [])) :: []) ->
      Dbrand (sexp_to_dbrands bs, sexp_to_data se')
  | STerm ("dtime_scale", [SString s]) ->
      Dforeign (Obj.magic (PrettyCommon.foreign_data_of_string s))
  | STerm (t, _) ->
      raise (Jura_Error ("Not well-formed S-expr with name " ^ t))
and sexp_to_drec (sel:sexp) : (char list * Data.qdata) =
  match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside drec")

(* Operators Section *)

let arithbop_to_sexp (b:arith_binary_op) : sexp =
  STerm (PrettyCommon.string_of_arith_binary_op b,[])
  
let sexp_to_arithbop (se:sexp) : arith_binary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.arith_binary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith binary_op")
  
let binary_op_to_sexp (b:binary_op) : sexp =
  match b with
  | OpEqual -> STerm ("AEq",[])
  | OpBagUnion -> STerm ("AUnion",[])
  | OpRecConcat -> STerm ("AConcat",[])
  | OpRecMerge -> STerm ("AMergeConcat",[])
  | OpAnd -> STerm ("AAnd",[])
  | OpOr -> STerm ("AOr",[])
  | OpArithBinary ab -> STerm ("ABArith",[arithbop_to_sexp ab])
  | OpLt -> STerm ("ALt",[])
  | OpLe -> STerm ("ALe",[])
  | OpBagDiff -> STerm ("AMinus",[])
  | OpBagMin -> STerm ("AMin",[])
  | OpBagMax -> STerm ("AMax",[])
  | OpContains -> STerm ("AContains",[])
  | OpStringConcat -> STerm ("ASConcat",[])
  | OpForeignBinary fbop -> SString (PrettyCommon.string_of_foreign_binary_op (Obj.magic fbop))

let sexp_to_binary_op (se:sexp) : binary_op =
  match se with
  | STerm ("AEq",[]) -> OpEqual
  | STerm ("AUnion",[]) -> OpBagUnion
  | STerm ("AConcat",[]) -> OpRecConcat
  | STerm ("AMergeConcat",[]) -> OpRecMerge
  | STerm ("AAnd",[]) -> OpAnd
  | STerm ("AOr",[]) -> OpOr
  | STerm ("ABArith",[se']) -> OpArithBinary (sexp_to_arithbop se')
  | STerm ("ALt",[]) -> OpLt
  | STerm ("ALe",[]) -> OpLe
  | STerm ("AMinus",[]) -> OpBagDiff
  | STerm ("AMin",[]) -> OpBagMin
  | STerm ("AMax",[]) -> OpBagMax
  | STerm ("AContains",[]) -> OpContains
  | STerm ("ASConcat",[]) -> OpStringConcat
  | SString fbop -> OpForeignBinary (Obj.magic (PrettyCommon.foreign_binary_op_of_string fbop))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("AFloatPlus",[]) -> Enhanced.Ops.Binary.coq_OpFloatPlus
  | STerm ("AFloatMinus",[]) -> Enhanced.Ops.Binary.coq_OpFloatMinus
  | STerm ("AFloatMult",[]) -> Enhanced.Ops.Binary.coq_OpFloatMult
  | STerm ("AFloatDiv",[]) -> Enhanced.Ops.Binary.coq_OpFloatDiv
  | STerm ("AFloatPow",[]) -> Enhanced.Ops.Binary.coq_OpFloatPow
  | STerm ("AFloatMin",[]) -> Enhanced.Ops.Binary.coq_OpFloatMin
  | STerm ("AFloatMax",[]) -> Enhanced.Ops.Binary.coq_OpFloatMax
  | STerm ("AFloatNe",[]) -> Enhanced.Ops.Binary.coq_OpFloatNe
  | STerm ("AFloatLt",[]) -> Enhanced.Ops.Binary.coq_OpFloatLt
  | STerm ("AFloatLe",[]) -> Enhanced.Ops.Binary.coq_OpFloatLe
  | STerm ("AFloatGt",[]) -> Enhanced.Ops.Binary.coq_OpFloatGt
  | STerm ("AFloatGe",[]) -> Enhanced.Ops.Binary.coq_OpFloatGe
  | STerm ("ATimeAs",[]) -> Enhanced.Ops.Binary.coq_OpTimeAs
  | STerm ("ATimeShift",[]) -> Enhanced.Ops.Binary.coq_OpTimeShift
  | STerm ("ATimeNe",[]) -> Enhanced.Ops.Binary.coq_OpTimeNe
  | STerm ("ATimeLt",[]) -> Enhanced.Ops.Binary.coq_OpTimeLt
  | STerm ("ATimeLe",[]) -> Enhanced.Ops.Binary.coq_OpTimeLe
  | STerm ("ATimeGt",[]) -> Enhanced.Ops.Binary.coq_OpTimeGt
  | STerm ("ATimeGe",[]) -> Enhanced.Ops.Binary.coq_OpTimeGe
  | STerm ("ATimeDurationFromScale",[]) -> Enhanced.Ops.Binary.coq_OpTimeDurationFromScale
  | STerm ("ATimeDurationBetween",[]) -> Enhanced.Ops.Binary.coq_OpTimeDurationBetween
  | STerm ("ADatePlus",[]) -> Enhanced.Ops.Binary.coq_OpSqlDatePlus
  | STerm ("ADateMinus",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateMinus
  | STerm ("ADateNe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateNe
  | STerm ("ADateLt",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateLt
  | STerm ("ADateLe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateLe
  | STerm ("ADateGt",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateGt
  | STerm ("ADateGe",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateGe
  | STerm ("ADateIntervalBetween",[]) -> Enhanced.Ops.Binary.coq_OpSqlDateIntervalBetween
  | STerm (t, _) ->
      raise (Jura_Error ("Not well-formed S-expr inside arith binary_op with name " ^ t))
  | _ -> raise  (Jura_Error "Not well-formed S-expr inside arith binary_op")

let arith_unary_op_to_sexp (b:arith_unary_op) : sexp =
  STerm (PrettyCommon.string_of_arith_unary_op b,[])

let sexp_to_arith_unary_op (se:sexp) : arith_unary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.arith_unary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith unary_op")

let unary_op_to_sexp (u:unary_op) : sexp =
  match u with
  | OpIdentity -> STerm ("AIdOp",[])
  | OpArithUnary au -> STerm ("AUArith", [arith_unary_op_to_sexp au])
  | OpNeg -> STerm ("ANeg",[])
  | OpBag -> STerm ("AColl",[])
  | OpCount -> STerm ("ACount",[])
  | OpFlatten -> STerm ("AFlatten",[])
  | OpLeft -> STerm ("ALeft",[])
  | OpRight -> STerm ("ARight",[])
  | OpBrand bl -> STerm ("ABrand", dbrands_to_sexp bl)
  | OpRec s -> STerm ("ARec", [coq_string_to_sstring s])
  | OpDot s -> STerm ("ADot", [coq_string_to_sstring s])
  | OpRecRemove s -> STerm ("ARecRemove", [coq_string_to_sstring s])
  | OpRecProject sl -> STerm ("ARecProject", coq_string_list_to_sstring_list sl)
  | OpDistinct -> STerm ("ADistinct",[])
  | OpOrderBy sl -> STerm ("AOrderBy", coq_string_list_to_sstring_list_with_order sl)
  | OpSum -> STerm ("ASum",[])
  | OpNumMean -> STerm ("AArithMean",[])
  | OpToString -> STerm ("AToString",[])
  | OpSubstring (n,None) -> STerm ("ASubstring",[SInt n])
  | OpSubstring (n1,(Some n2)) -> STerm ("ASubstring",[SInt n1;SInt n2])
  | OpLike (p,None) -> STerm ("ALike",[coq_string_to_sstring p])
  | OpLike (p,(Some esc)) -> STerm ("ALike",[coq_string_to_sstring p;coq_string_to_sstring [esc]])
  | OpCast bl -> STerm ("ACast", dbrands_to_sexp bl)
  | OpUnbrand -> STerm ("AUnbrand",[])
  | OpSingleton -> STerm ("ASingleton",[])
  | OpNumMin -> STerm ("ANumMin",[])
  | OpNumMax -> STerm ("ANumMax",[])
  | OpForeignUnary fuop -> SString (PrettyCommon.string_of_foreign_unary_op (Obj.magic fuop))

let sstring_to_sql_date_component (part:sexp) : Enhanced.Data.sql_date_part =
  match part with
  | SString "DAY" ->   Enhanced.Data.sql_date_day
  | SString "MONTH" -> Enhanced.Data.sql_date_month
  | SString "YEAR" ->  Enhanced.Data.sql_date_year
  | _ -> raise (Jura_Error "Not well-formed S-expr for sql date component")
			  
let sexp_to_unary_op (se:sexp) : unary_op =
  match se with
  | STerm ("AIdOp",[]) -> OpIdentity
  | STerm ("AUArith", [se']) ->
      let au = sexp_to_arith_unary_op se' in
      OpArithUnary au
  | STerm ("ANeg",[]) -> OpNeg
  | STerm ("AColl",[]) -> OpBag
  | STerm ("ACount",[]) -> OpCount
  | STerm ("AFlatten",[]) -> OpFlatten
  | STerm ("ALeft",[]) -> OpLeft
  | STerm ("ARight",[]) -> OpRight
  | STerm ("ABrand", bl) -> OpBrand (sexp_to_dbrands bl)
  | STerm ("ARec", [se']) -> OpRec (sstring_to_coq_string se')
  | STerm ("ADot", [se']) -> OpDot (sstring_to_coq_string se')
  | STerm ("ARecRemove", [se']) -> OpRecRemove (sstring_to_coq_string se')
  | STerm ("ARecProject", sl) -> OpRecProject (sstring_list_to_coq_string_list sl)
  | STerm ("ADistinct",[]) -> OpDistinct
  | STerm ("AOrderBy",sl) -> OpOrderBy (sstring_list_with_order_to_coq_string_list sl)
  | STerm ("ASum",[]) -> OpSum
  | STerm ("AArithMean",[]) -> OpNumMean
  | STerm ("AToString",[]) -> OpToString
  | STerm ("ASubstring",[SInt n1]) -> OpSubstring (n1,None)
  | STerm ("ASubstring",[SInt n1;SInt n2]) -> OpSubstring (n1,Some n2)
  | STerm ("ALike",[p]) -> OpLike (sstring_to_coq_string p,None)
  | STerm ("ALike",[p;SString esc]) ->
     OpLike (sstring_to_coq_string p,Some (esc.[0]))
  | STerm ("ACast", bl) -> OpCast (sexp_to_dbrands bl)
  | STerm ("AUnbrand",[]) -> OpUnbrand
  | STerm ("ASingleton",[]) -> OpSingleton
  | STerm ("ANumMin",[]) -> OpNumMin
  | STerm ("ANumMax",[]) -> OpNumMax
  | SString s -> OpForeignUnary (Obj.magic (PrettyCommon.foreign_unary_op_of_string s))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("AFloatNeg",[]) -> Enhanced.Ops.Unary.coq_OpFloatNeg
  | STerm ("AFloatSqrt",[]) -> Enhanced.Ops.Unary.coq_OpFloatSqrt
  | STerm ("AFloatExp",[]) -> Enhanced.Ops.Unary.coq_OpFloatExp
  | STerm ("AFloatLog",[]) -> Enhanced.Ops.Unary.coq_OpFloatLog
  | STerm ("AFloatLog10",[]) -> Enhanced.Ops.Unary.coq_OpFloatLog10
  | STerm ("AFloatOfInt",[]) -> Enhanced.Ops.Unary.coq_OpFloatOfInt
  | STerm ("AFloatCeil",[]) -> Enhanced.Ops.Unary.coq_OpFloatCeil
  | STerm ("AFloatFloor",[]) -> Enhanced.Ops.Unary.coq_OpFloatFloor
  | STerm ("AFloatTruncate",[]) -> Enhanced.Ops.Unary.coq_OpFloatTruncate
  | STerm ("AFloatAbs",[]) -> Enhanced.Ops.Unary.coq_OpFloatAbs
  | STerm ("AFloatSum",[]) -> Enhanced.Ops.Unary.coq_OpFloatSum
  | STerm ("AFloatArithMean",[]) -> Enhanced.Ops.Unary.coq_OpFloatArithMean
  | STerm ("AFloatListMin",[]) -> Enhanced.Ops.Unary.coq_OpFloatListMin
  | STerm ("AFloatListMax",[]) -> Enhanced.Ops.Unary.coq_OpFloatListMax
  | STerm ("ATimeToSscale",[]) -> Enhanced.Ops.Unary.coq_OpTimeToSscale
  | STerm ("ATimeFromString",[]) -> Enhanced.Ops.Unary.coq_OpTimeFromString
  | STerm ("ATimeDurationFromString",[]) -> Enhanced.Ops.Unary.coq_OpTimeDurationFromString
  | STerm ("ADateFromString",[]) -> Enhanced.Ops.Unary.coq_OpSqlDateFromString
  | STerm ("ADateIntervalromString",[]) -> Enhanced.Ops.Unary.coq_OpSqlDateIntervalFromString
  | STerm ("AGetDateComponent",[part]) -> Enhanced.Ops.Unary.coq_OpSqlGetDateComponent (sstring_to_sql_date_component part)
  | STerm (t, _) ->
      raise (Jura_Error ("Not well-formed S-expr inside unary_op with name " ^ t))
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside unary_op")


(* NNRC Section *)

let rec nnrc_to_sexp (n : nnrc) : sexp =
  match n with
  | NNRCGetConstant v -> STerm ("GetConstant", [SString (string_of_char_list v)])
  | NNRCVar v -> STerm ("Var", [SString (string_of_char_list v)])
  | NNRCConst d -> STerm ("Const", [data_to_sexp d])
  | NNRCBinop (b, n1, n2) -> STerm ("Binop", (binary_op_to_sexp b) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCUnop (u, n1) -> STerm ("Unop", (unary_op_to_sexp u) :: [nnrc_to_sexp n1])
  | NNRCLet (v, n1, n2) -> STerm ("Let", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCFor (v, n1, n2) -> STerm ("For", (SString (string_of_char_list v)) :: [nnrc_to_sexp n1;nnrc_to_sexp n2])
  | NNRCIf (n1, n2, n3) -> STerm ("If", [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])
  | NNRCEither (n1,v1,n2,v2,n3) -> STerm ("Either",
					 (SString (string_of_char_list v1))
					 :: (SString (string_of_char_list v2))
					 :: [nnrc_to_sexp n1;nnrc_to_sexp n2;nnrc_to_sexp n3])
  | NNRCGroupBy (g,sl,n1) -> STerm ("GroupBy",
				    (SString (string_of_char_list g))
				    :: (STerm ("keys",coq_string_list_to_sstring_list sl))
				    :: [nnrc_to_sexp n1])

let rec sexp_to_nnrc (se:sexp) : nnrc =
  match se with
  | STerm ("GetConstant", [SString v]) -> NNRCGetConstant (char_list_of_string v)
  | STerm ("Var", [SString v]) -> NNRCVar (char_list_of_string v)
  | STerm ("Const", [d]) -> NNRCConst (sexp_to_data d)
  | STerm ("Binop", b :: [n1;n2]) -> NNRCBinop (sexp_to_binary_op b, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("Unop", u :: [n1]) -> NNRCUnop (sexp_to_unary_op u, sexp_to_nnrc n1)
  | STerm ("Let", (SString v) :: [n1;n2]) -> NNRCLet (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("For", (SString v) :: [n1;n2]) -> NNRCFor (char_list_of_string v, sexp_to_nnrc n1, sexp_to_nnrc n2)
  | STerm ("If", [n1;n2;n3]) -> NNRCIf (sexp_to_nnrc n1, sexp_to_nnrc n2, sexp_to_nnrc n3)
  | STerm ("Either", (SString v1) :: (SString v2) :: [n1;n2;n3]) ->
      NNRCEither (sexp_to_nnrc n1,char_list_of_string v1,sexp_to_nnrc n2,char_list_of_string v2,sexp_to_nnrc n3)
  | STerm ("GroupBy", (SString v1) :: (STerm ("keys", v2)) :: [n1]) ->
      NNRCGroupBy (char_list_of_string v1,sstring_list_to_coq_string_list v2,sexp_to_nnrc n1)
  | STerm (t, _) ->
      raise (Jura_Error ("Not well-formed S-expr inside nnrc with name " ^ t))
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside nnrc")

(* JuraC section *)

let name_to_sexp name =
  (SString (string_of_char_list name))
let sexp_to_name (se:sexp) =
  begin match se with
  | SString s -> char_list_of_string s
  | _ -> 
      raise (Jura_Error "Not well-formed S-expr inside name")
  end

let param_to_sexp (paramname,paramtypename) =
  let pname = name_to_sexp paramname in
  let ptname = name_to_sexp paramtypename in
  STerm ("Param",[pname;ptname])
let params_to_sexp params =
  let params = List.map param_to_sexp params in
  STerm ("Params",params)

let sexp_to_param (se:sexp) =
  begin match se with
  | STerm ("Param",[spname;sptname]) ->
      (sexp_to_name spname, sexp_to_name sptname)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Param")
  end
let sexp_to_params (se:sexp) =
  begin match se with
  | STerm ("Params", sparams) ->
      List.map sexp_to_param sparams
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Params")
  end

let maythrow_to_sexp th : sexp =
  begin match th with
  | None -> STerm ("MayThrow",[])
  | Some tn -> STerm ("MayThrow", [name_to_sexp tn])
  end

let sexp_to_maythrow (se:sexp) =
  begin match se with
  | STerm ("MayThrow",[]) -> None
  | STerm ("MayThrow",[stn]) -> Some (sexp_to_name stn)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside MayThrow")
  end

let clause_to_sexp (expr_to_sexp : 'a -> sexp) (cl:'a clause) =
  let clname = name_to_sexp cl.clause_name in
  let clparams = params_to_sexp cl.clause_params in
  let cloutput = name_to_sexp cl.clause_output in
  let clthrow = maythrow_to_sexp cl.clause_throw in
  let clcode = expr_to_sexp cl.clause_code in
  STerm ("Clause",[clname;clparams;cloutput;clthrow;clcode])

let sexp_to_clause (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a clause =
  begin match se with
  | STerm ("Clause",[sclname;sclparams;scloutput;sclthrow;sclcode]) ->
      { clause_name = sexp_to_name sclname;
	clause_params = sexp_to_params sclparams;
	clause_output = sexp_to_name scloutput;
	clause_throw = sexp_to_maythrow sclthrow;
	clause_code = sexp_to_expr sclcode }
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Clause")
  end

let declaration_to_sexp (expr_to_sexp : 'a -> sexp) (dl:'a declaration) =
  STerm ("Declaration",[clause_to_sexp expr_to_sexp dl])
let declarations_to_sexp (expr_to_sexp : 'a -> sexp) (dls:'a declaration list) =
  let decls = List.map (declaration_to_sexp expr_to_sexp) dls in
  STerm ("Declarations",decls)

let sexp_to_declaration (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a declaration =
  begin match se with
  | STerm ("Declaration",[secl]) ->
      sexp_to_clause sexp_to_expr secl
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Declaration")
  end
let sexp_to_declarations (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a declaration list =
  begin match se with
  | STerm ("Declarations",sdecls) ->
      List.map (sexp_to_declaration sexp_to_expr) sdecls
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Declarations")
  end

let contract_to_sexp (expr_to_sexp : 'a -> sexp) (c:'a contract) =
  let cname = name_to_sexp c.contract_name in
  let tname = name_to_sexp c.contract_template in
  let decls = declarations_to_sexp expr_to_sexp c.contract_declarations in
  STerm ("Contract", [cname;tname;decls])

let sexp_to_contract (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a contract =
  begin match se with
  | STerm ("Contract",[scname;stname;sdecls]) ->
      { contract_name = sexp_to_name scname;
	contract_template = sexp_to_name stname;
        contract_declarations = sexp_to_declarations sexp_to_expr sdecls; }
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Contract")
  end

let import_to_sexp i =
  SString (string_of_char_list i)
let imports_to_sexp is =
  let imports = List.map import_to_sexp is in
  STerm ("Imports",imports)

let sexp_to_import (se:sexp) =
  begin match se with
  | SString s -> char_list_of_string s
  | _ -> 
      raise (Jura_Error "Not well-formed S-expr inside import")
  end
let sexp_to_imports (se:sexp) =
  begin match se with
  | STerm ("Imports",sis) ->
      List.map sexp_to_import sis
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Imports")
  end

let package_to_sexp (expr_to_sexp : 'a -> sexp) (p:'a package) =
  let pname = name_to_sexp p.package_name in
  let imports = imports_to_sexp p.package_imports in
  let contract = contract_to_sexp expr_to_sexp p.package_contract in
  STerm ("Package", [pname;imports;contract])

let sexp_to_package (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a package =
  begin match se with
  | STerm ("Package",[spname;simports;scontract]) ->
      { package_name = sexp_to_name spname;
	package_imports = sexp_to_imports simports;
	package_contract = sexp_to_contract sexp_to_expr scontract; }
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Package")
  end

let jurac_expr_to_sexp = nnrc_to_sexp
let jurac_package_to_sexp (p:jurac_package) : sexp =
  STerm ("JuraCalculus", [package_to_sexp jurac_expr_to_sexp p])

let sexp_to_jurac_expr = sexp_to_nnrc
let sexp_to_jurac_package (se:sexp) : jurac_package =
  begin match se with
  | STerm ("JuraCalculus",[spackage]) ->
      sexp_to_package sexp_to_jurac_expr spackage
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside JuraCalculus")
  end
  

