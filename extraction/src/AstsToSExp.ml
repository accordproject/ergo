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
open JuraEnhancedBackend
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
  | Enhancedstring s -> STerm ("enhanced_string", (SString s)::[])
  | Enhancedtimescale ts -> STerm ("dtime_scale", (SString (PrettyCommon.timescale_as_string ts))::[])
  | Enhancedtimeduration td -> raise Not_found
  | Enhancedtimepoint tp -> raise Not_found
  | Enhancedsqldate td -> raise Not_found
  | Enhancedsqldateinterval tp -> raise Not_found

let rec data_to_sexp (d : JuraData.data) : sexp =
  match d with
  | Dunit -> STerm ("dunit", [])
  | Dnat n -> SInt n
  | Dfloat f -> SFloat f
  | Dbool b -> SBool b
  | Dstring s -> SString (string_of_char_list s)
  | Dcoll dl -> STerm ("dcoll", List.map data_to_sexp dl)
  | Drec adl -> STerm ("drec", List.map drec_to_sexp adl)
  | Dleft d -> STerm ("dleft", data_to_sexp d :: [])
  | Dright d -> STerm ("dright", data_to_sexp d :: [])
  | Dbrand (bs,d) -> STerm ("dbrand", (STerm ("brands", dbrands_to_sexp bs)) :: (STerm ("value", (data_to_sexp d) :: [])) :: [])
  | Dforeign fdt -> foreign_data_to_sexp (Obj.magic fdt)
and drec_to_sexp (ad : char list * JuraData.data) : sexp =
  STerm ("datt", (SString (string_of_char_list (fst ad))) :: (data_to_sexp (snd ad)) :: [])

let rec sexp_to_data (se:sexp) : JuraData.data =
  match se with
  | STerm ("dunit", []) -> Dunit
  | SBool b -> Dbool b
  | SInt n -> Dnat n
  | SFloat f -> Dfloat f
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
and sexp_to_drec (sel:sexp) : (char list * JuraData.data) =
  match sel with
  | STerm ("datt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_data se)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside drec")

(* Operators Section *)

let nat_arith_bop_to_sexp (b:nat_arith_binary_op) : sexp =
  STerm (PrettyCommon.string_of_nat_arith_binary_op b,[])
  
let sexp_to_nat_arith_bop (se:sexp) : nat_arith_binary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.nat_arith_binary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith nat arith binary_op")
  
let float_arith_bop_to_sexp (b:float_arith_binary_op) : sexp =
  STerm (PrettyCommon.string_of_float_arith_binary_op b,[])
  
let float_compare_bop_to_sexp (b:float_compare_binary_op) : sexp =
  STerm (PrettyCommon.string_of_float_compare_binary_op b,[])
  
let sexp_to_float_arith_bop (se:sexp) : float_arith_binary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.float_arith_binary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith float arith binary_op")
  
let sexp_to_float_compare_bop (se:sexp) : float_compare_binary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.float_compare_binary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith float compare binary_op")

let binary_op_to_sexp (b:binary_op) : sexp =
  match b with
  | OpEqual -> STerm ("AEq",[])
  | OpBagUnion -> STerm ("AUnion",[])
  | OpRecConcat -> STerm ("AConcat",[])
  | OpRecMerge -> STerm ("AMergeConcat",[])
  | OpAnd -> STerm ("AAnd",[])
  | OpOr -> STerm ("AOr",[])
  | OpNatBinary ab -> STerm ("ABNat",[nat_arith_bop_to_sexp ab])
  | OpFloatBinary ab -> STerm ("ABFloat",[float_arith_bop_to_sexp ab])
  | OpFloatCompare ab -> STerm ("ABFloatCompare",[float_compare_bop_to_sexp ab])
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
  | STerm ("ABNat",[se']) -> OpNatBinary (sexp_to_nat_arith_bop se')
  | STerm ("ABFloat",[se']) -> OpFloatBinary (sexp_to_float_arith_bop se')
  | STerm ("ABFloatCompare",[se']) -> OpFloatCompare (sexp_to_float_compare_bop se')
  | STerm ("ALt",[]) -> OpLt
  | STerm ("ALe",[]) -> OpLe
  | STerm ("AMinus",[]) -> OpBagDiff
  | STerm ("AMin",[]) -> OpBagMin
  | STerm ("AMax",[]) -> OpBagMax
  | STerm ("AContains",[]) -> OpContains
  | STerm ("ASConcat",[]) -> OpStringConcat
  | SString fbop -> OpForeignBinary (Obj.magic (PrettyCommon.foreign_binary_op_of_string fbop))
  (* WARNING: Those are not printed, only parsed *)
  | STerm ("ATimeAs",[]) -> JuraOps.Binary.DateTime.optimeas
  | STerm ("ATimeShift",[]) -> JuraOps.Binary.DateTime.optimeshift
  | STerm ("ATimeNe",[]) -> JuraOps.Binary.DateTime.optimene
  | STerm ("ATimeLt",[]) -> JuraOps.Binary.DateTime.optimelt
  | STerm ("ATimeLe",[]) -> JuraOps.Binary.DateTime.optimele
  | STerm ("ATimeGt",[]) -> JuraOps.Binary.DateTime.optimegt
  | STerm ("ATimeGe",[]) -> JuraOps.Binary.DateTime.optimege
  | STerm ("ATimeDurationFromScale",[]) -> JuraOps.Binary.DateTime.optimedurationfromscale
  | STerm ("ATimeDurationBetween",[]) -> JuraOps.Binary.DateTime.optimedurationbetween
  | STerm ("ADatePlus",[]) -> JuraOps.Binary.DateTime.opdateplus
  | STerm ("ADateMinus",[]) -> JuraOps.Binary.DateTime.opdateminus
  | STerm ("ADateNe",[]) -> JuraOps.Binary.DateTime.opdatene
  | STerm ("ADateLt",[]) -> JuraOps.Binary.DateTime.opdatelt
  | STerm ("ADateLe",[]) -> JuraOps.Binary.DateTime.opdatele
  | STerm ("ADateGt",[]) -> JuraOps.Binary.DateTime.opdategt
  | STerm ("ADateGe",[]) -> JuraOps.Binary.DateTime.opdatege
  | STerm ("ADateIntervalBetween",[]) -> JuraOps.Binary.DateTime.opdateintervalbetween
  | STerm (t, _) ->
      raise (Jura_Error ("Not well-formed S-expr inside arith binary_op with name " ^ t))
  | _ -> raise  (Jura_Error "Not well-formed S-expr inside arith binary_op")

let nat_arith_unary_op_to_sexp (b:nat_arith_unary_op) : sexp =
  STerm (PrettyCommon.string_of_nat_arith_unary_op b,[])

let sexp_to_nat_arith_unary_op (se:sexp) : nat_arith_unary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.nat_arith_unary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith nat unary_op")

let float_arith_unary_op_to_sexp (b:float_arith_unary_op) : sexp =
  STerm (PrettyCommon.string_of_float_arith_unary_op b,[])

let sexp_to_float_arith_unary_op (se:sexp) : float_arith_unary_op =
  match se with
  | STerm (s,[]) -> PrettyCommon.float_arith_unary_op_of_string s
  | _ ->
      raise  (Jura_Error "Not well-formed S-expr inside arith float unary_op")

let unary_op_to_sexp (u:unary_op) : sexp =
  match u with
  | OpIdentity -> STerm ("AIdOp",[])
  | OpNatUnary au -> STerm ("AUNat", [nat_arith_unary_op_to_sexp au])
  | OpFloatUnary au -> STerm ("AUFloat", [float_arith_unary_op_to_sexp au])
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
  | OpNatSum -> STerm ("ANatSum",[])
  | OpNatMean -> STerm ("ANatMean",[])
  | OpNatMin -> STerm ("ANatMin",[])
  | OpNatMax -> STerm ("ANatMax",[])
  | OpFloatOfNat -> STerm ("AFloatOfNat",[])
  | OpFloatTruncate -> STerm ("AFloatTruncate",[])
  | OpFloatSum -> STerm ("AFloatSum",[])
  | OpFloatMean -> STerm ("AFloatMean",[])
  | OpFloatBagMin -> STerm ("AFloatBagMin",[])
  | OpFloatBagMax -> STerm ("AFloatBagMax",[])
  | OpToString -> STerm ("AToString",[])
  | OpSubstring (n,None) -> STerm ("ASubstring",[SInt n])
  | OpSubstring (n1,(Some n2)) -> STerm ("ASubstring",[SInt n1;SInt n2])
  | OpLike (p,None) -> STerm ("ALike",[coq_string_to_sstring p])
  | OpLike (p,(Some esc)) -> STerm ("ALike",[coq_string_to_sstring p;coq_string_to_sstring [esc]])
  | OpCast bl -> STerm ("ACast", dbrands_to_sexp bl)
  | OpUnbrand -> STerm ("AUnbrand",[])
  | OpSingleton -> STerm ("ASingleton",[])
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
  | STerm ("AUNat", [se']) ->
      let au = sexp_to_nat_arith_unary_op se' in
      OpNatUnary au
  | STerm ("AUFloat", [se']) ->
      let au = sexp_to_float_arith_unary_op se' in
      OpFloatUnary au
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
  | STerm ("AToString",[]) -> OpToString
  | STerm ("ASubstring",[SInt n1]) -> OpSubstring (n1,None)
  | STerm ("ASubstring",[SInt n1;SInt n2]) -> OpSubstring (n1,Some n2)
  | STerm ("ALike",[p]) -> OpLike (sstring_to_coq_string p,None)
  | STerm ("ALike",[p;SString esc]) ->
     OpLike (sstring_to_coq_string p,Some (esc.[0]))
  | STerm ("ACast", bl) -> OpCast (sexp_to_dbrands bl)
  | STerm ("AUnbrand",[]) -> OpUnbrand
  | STerm ("ASingleton",[]) -> OpSingleton
  | STerm ("ANatSum",[]) -> OpNatSum
  | STerm ("ANatMean",[]) -> OpNatMean
  | STerm ("ANatMin",[]) -> OpNatMin
  | STerm ("ANatMax",[]) -> OpNatMax
  | SString s -> OpForeignUnary (Obj.magic (PrettyCommon.foreign_unary_op_of_string s))
  | STerm ("AFloatOfNat",[]) -> OpFloatOfNat
  | STerm ("AFloatTruncate",[]) -> OpFloatTruncate
  | STerm ("AFloatSum",[]) -> OpFloatSum
  | STerm ("AFloatMean",[]) -> OpFloatMean
  | STerm ("AFloatBagMin",[]) -> OpFloatBagMin
  | STerm ("AFloatBagMax",[]) -> OpFloatBagMax
  (* WARNING: Those are not printed, only parsed *)
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

let opt_name_to_sexp name =
  begin match name with
  | None -> STerm ("Name", [])
  | Some name -> STerm ("Name", [(SString (string_of_char_list name))])
  end
let sexp_to_opt_name (se:sexp) =
  begin match se with
  | STerm ("Name", []) -> None
  | STerm ("Name", [SString s]) -> Some (char_list_of_string s)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside optional name")
  end

let list_name_to_sexp names =
  STerm ("Names",List.map name_to_sexp names)
let sexp_to_list_name (se:sexp) =
  begin match se with
  | STerm ("Names", senames) -> List.map sexp_to_name senames
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside list name")
  end

let class_ref_to_sexp cr =
  let ns = cr.class_namespace in
  let cln = cr.class_name in
  STerm ("ClassRef",[opt_name_to_sexp ns; name_to_sexp cln])
let sexp_to_class_ref se =
  begin match se with
  | STerm ("ClassRef",[sens;secln]) ->
    { class_namespace = sexp_to_opt_name sens;
      class_name = sexp_to_name secln }
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside class ref")
  end

let rec paramtype_to_sexp (pt:cto_type) =
  begin match pt with
  | CTOBoolean -> STerm ("CTOBoolean", [])
  | CTOString -> STerm ("CTOString", [])
  | CTODouble -> STerm ("CTODouble", [])
  | CTOLong -> STerm ("CTOLong", [])
  | CTOInteger -> STerm ("CTOInteger", [])
  | CTODateTime -> STerm ("CTODateTime", [])
  | CTOClassRef clt -> STerm ("CTOClassRef", [class_ref_to_sexp clt])
  | CTOOption pt -> STerm ("CTOption", [paramtype_to_sexp pt])
  | CTORecord rt -> STerm ("CTORecord", rectype_to_sexp rt)
  | CTOArray pt -> STerm ("CTOArray", [paramtype_to_sexp pt])
  end
and rectype_to_sexp (rt : (char list * cto_type) list) : sexp list =
  List.map atttype_to_sexp rt
and atttype_to_sexp (at : char list * cto_type) : sexp =
  STerm ("tatt", (SString (string_of_char_list (fst at))) :: (paramtype_to_sexp (snd at)) :: [])
let rec sexp_to_paramtype (se:sexp) =
  begin match se with
  | STerm ("CTOBoolean", []) -> CTOBoolean
  | STerm ("CTOString", []) -> CTOString
  | STerm ("CTODouble", []) -> CTODouble
  | STerm ("CTOLong", []) -> CTOLong
  | STerm ("CTOInteger", []) -> CTOInteger
  | STerm ("CTODateTime", []) -> CTODateTime
  | STerm ("CTOClassRef", [cl]) -> CTOClassRef (sexp_to_class_ref cl)
  | STerm ("CTOption", [pt]) -> CTOOption (sexp_to_paramtype pt)
  | STerm ("CTORecord", rt) -> CTORecord (sexp_to_rectype rt)
  | STerm ("CTOArray", [pt]) -> CTOArray (sexp_to_paramtype pt)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside ParamType")
  end
and sexp_to_rectype (ser:sexp list) : (char list * cto_type) list =
  List.map sexp_to_atttype ser
and sexp_to_atttype (sea:sexp) : (char list * cto_type) =
  match sea with
  | STerm ("tatt", (SString s) :: se :: []) ->
      (char_list_of_string s, sexp_to_paramtype se)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside CTORecord")

let opt_paramtype_to_sexp (opt:cto_type option) =
  begin match opt with
  | None -> STerm ("ParamType",[])
  | Some pt -> STerm ("ParamType",[paramtype_to_sexp pt])
  end
let sexp_to_opt_paramtype (se:sexp) =
  begin match se with
  | STerm ("ParamType",[]) -> None
  | STerm ("ParamType",[pt]) -> Some (sexp_to_paramtype pt)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside OptParamType")
  end

let param_to_sexp (paramname,paramtype) =
  let pname = name_to_sexp paramname in
  STerm ("Param",[pname;opt_paramtype_to_sexp paramtype])
let params_to_sexp params =
  let params = List.map param_to_sexp params in
  STerm ("Params",params)

let sexp_to_param (se:sexp) =
  begin match se with
  | STerm ("Param",[spname;sptname]) ->
      (sexp_to_name spname, sexp_to_opt_paramtype sptname)
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

let closure_to_sexp (expr_to_sexp : 'a -> sexp) (cl:'a closure0) =
  let clparams = params_to_sexp cl.closure_params0 in
  let cloutput = opt_paramtype_to_sexp cl.closure_output0 in
  let clthrow = opt_name_to_sexp cl.closure_throw in
  let clbody = expr_to_sexp cl.closure_body0 in
  STerm ("Closure",[clparams;cloutput;clthrow;clbody])
let sexp_to_closure (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a closure0 =
  begin match se with
  | STerm ("Closure",[sclparams;scloutput;sclthrow;sclbody]) ->
      { closure_params0 = sexp_to_params sclparams;
	closure_output0 = sexp_to_opt_paramtype scloutput;
	closure_throw = sexp_to_opt_name sclthrow;
	closure_body0 = sexp_to_expr sclbody }
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Closure")
  end

let declaration_to_sexp (expr_to_sexp : 'a -> sexp) (d:'a declaration) =
  begin match d with
  | Clause c ->
      let clname = name_to_sexp c.clause_name in
      let clclosure = closure_to_sexp expr_to_sexp c.clause_closure in
      STerm ("Clause",[clname;clclosure])
  | Func f ->
      let fname = name_to_sexp f.func_name in
      let fclosure = closure_to_sexp expr_to_sexp f.func_closure in
      STerm ("Func",[fname;fclosure])
  end
let declarations_to_sexp (expr_to_sexp : 'a -> sexp) (dls:'a declaration list) =
  let decls = List.map (declaration_to_sexp expr_to_sexp) dls in
  STerm ("Declarations",decls)

let sexp_to_declaration (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a declaration =
  begin match se with
  | STerm ("Clause",[sclname;sclclosure]) ->
      Clause
	{ clause_name = sexp_to_name sclname;
	  clause_closure = sexp_to_closure sexp_to_expr sclclosure }
  | STerm ("Func",[sfname;sfclosure]) ->
      Func
	{ func_name = sexp_to_name sfname;
	  func_closure = sexp_to_closure sexp_to_expr sfclosure }
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
let sexp_to_import (se:sexp) =
  begin match se with
  | SString s -> char_list_of_string s
  | _ -> 
      raise (Jura_Error "Not well-formed S-expr inside Import")
  end

let cto_type_to_sexp t =
  begin match t with
  | CTOEnum ln -> STerm ("CTOEnum", [list_name_to_sexp ln])
  | CTOTransaction (oe,rectype) ->
    STerm ("CTOTransaction",[opt_name_to_sexp oe;
                             STerm ("CTORecord",rectype_to_sexp rectype)])
  | CTOConcept (oe,rectype) ->
    STerm ("CTOConcept",[opt_name_to_sexp oe;
                         STerm ("CTORecord",rectype_to_sexp rectype)])
  end
let sexp_to_cto_type (se:sexp) =
  begin match se with
  | STerm ("CTOEnum", [seln]) -> CTOEnum (sexp_to_list_name seln)
  | STerm ("CTOTransaction",[sen;STerm ("CTORecord",serectype)]) ->
    CTOTransaction (sexp_to_opt_name sen,
                    sexp_to_rectype serectype)
  | STerm ("CTOConcept",[sen;STerm ("CTORecord",serectype)]) ->
    CTOConcept (sexp_to_opt_name sen,
                sexp_to_rectype serectype)
  | _ -> 
    raise (Jura_Error "Not well-formed S-expr inside CTO type declaration")
  end

let stmt_to_sexp (expr_to_sexp : 'a -> sexp) (s:'a stmt) =
  begin match s with
  | JType cto_decl ->
    STerm ("JType",[class_ref_to_sexp cto_decl.cto_declaration_class;
                    cto_type_to_sexp cto_decl.cto_declaration_type])
  | JExpr e ->
      STerm ("JExpr",[expr_to_sexp e])
  | JGlobal (v, e) ->
      STerm ("JGlobal",[name_to_sexp v;expr_to_sexp e])
  | JImport i ->
      STerm ("JImport",[import_to_sexp i])
  | JFunc f ->
      let fname = name_to_sexp f.func_name in
      let fclosure = closure_to_sexp expr_to_sexp f.func_closure in
      STerm ("JFunc",[fname;fclosure])
  | JContract c ->
      STerm ("JContract",[contract_to_sexp expr_to_sexp c])
  end
let stmts_to_sexp (expr_to_sexp : 'a -> sexp) (ss:'a stmt list) =
  let sss = List.map (stmt_to_sexp expr_to_sexp) ss in
  STerm ("Stmts",sss)

let sexp_to_stmt (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a stmt =
  begin match se with
  | STerm ("JType",[soname; scto_type]) ->
      JType (JuraCompiler.mk_cto_declaration (sexp_to_class_ref soname) (sexp_to_cto_type scto_type))
  | STerm ("JExpr",[se]) ->
      JExpr (sexp_to_expr se)
  | STerm ("JGlobal",[svname;se]) ->
      JGlobal (sexp_to_name svname, sexp_to_expr se)
  | STerm ("JImport",[si]) ->
      JImport (sexp_to_import si)
  | STerm ("JFunc",[sfname;sfclosure]) ->
      JFunc
	{ func_name = sexp_to_name sfname;
	  func_closure = sexp_to_closure sexp_to_expr sfclosure }
  | STerm ("JContract",[sc]) ->
      JContract (sexp_to_contract sexp_to_expr sc)
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Stmt")
  end
let sexp_to_stmts (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a stmt list =
  begin match se with
  | STerm ("Stmts",sss) ->
      List.map (sexp_to_stmt sexp_to_expr) sss
  | _ ->
      raise (Jura_Error "Not well-formed S-expr inside Stmts")
  end

let package_to_sexp (expr_to_sexp : 'a -> sexp) (p:'a package) =
  let namespace = opt_name_to_sexp p.package_namespace in
  let stmts = stmts_to_sexp expr_to_sexp p.package_statements in
  STerm ("Package", [namespace;stmts])

let sexp_to_package (sexp_to_expr : sexp -> 'a) (se:sexp) : 'a package =
  begin match se with
  | STerm ("Package",[snamespace;sstmts]) ->
      { package_namespace = sexp_to_opt_name snamespace;
	package_statements = sexp_to_stmts sexp_to_expr sstmts; }
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
  
