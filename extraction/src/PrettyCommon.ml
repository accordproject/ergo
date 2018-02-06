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

open Format
open JComp
open JuraCompiler

let timescale_as_string ts =
  match ts with
  | Ts_second -> "SECOND"
  | Ts_minute ->  "MINUTE"
  | Ts_hour -> "HOUR"
  | Ts_day -> "DAY"
  | Ts_week -> "WEEK"
  | Ts_month -> "MONTH"
  | Ts_year -> "YEAR"

let string_of_foreign_data (fd:enhanced_data) : string =
  match fd with
  | Enhancedfloat f -> string_of_float f
  | Enhancedstring s -> "S\"" ^ s ^ "\""
  | Enhancedtimescale ts -> timescale_as_string ts
  | Enhancedtimeduration td -> raise Not_found
  | Enhancedtimepoint tp -> raise Not_found
  | Enhancedsqldate td -> raise Not_found
  | Enhancedsqldateinterval tp -> raise Not_found

let foreign_data_of_string s =
  try
    Enhancedfloat (float_of_string s)
  with
  | Failure _ ->
      begin
	match s with
	| "SECOND" -> Enhancedtimescale Ts_second
	| "MINUTE" -> Enhancedtimescale Ts_minute
	| "HOUR" -> Enhancedtimescale Ts_hour
	| "DAY" -> Enhancedtimescale Ts_day
	| "WEEK" -> Enhancedtimescale Ts_week
	| "MONTH" -> Enhancedtimescale Ts_month
	| "YEAR" -> Enhancedtimescale Ts_year
	| _ ->
	    try
	      if (s.[0] = 'S' && s.[1] = '"')
	      then
		Enhancedstring (String.sub s 2 ((String.length s) - 3))
	      else
		raise Not_found
	    with
	    | _ ->
		raise Not_found
      end

let string_of_arith_unary_op ua =
  match ua with
  | ArithAbs -> "abs"
  | ArithLog2 -> "log2"
  | ArithSqrt -> "sqrt"

let arith_unary_op_of_string s =
  match s with
  | "abs" -> ArithAbs
  | "log2" -> ArithLog2
  | "sqrt" -> ArithSqrt
  | _ -> raise Not_found

let sql_date_component_to_string part =
  match part with
  | Sql_date_DAY -> "DAY"
  | Sql_date_MONTH -> "MONTH"
  | Sql_date_YEAR -> "YEAR"

let string_of_foreign_unary_op fu : string =
  match fu with
  | Enhanced_unary_float_op Uop_float_neg -> "Fneg"
  | Enhanced_unary_float_op Uop_float_sqrt -> "Fsqrt"
  | Enhanced_unary_float_op Uop_float_exp -> "Fexp"
  | Enhanced_unary_float_op Uop_float_log -> "Flog"
  | Enhanced_unary_float_op Uop_float_log10 -> "Flog10"
  | Enhanced_unary_float_op Uop_float_of_int -> "Fof_int"
  | Enhanced_unary_float_op Uop_float_ceil -> "Fceil"
  | Enhanced_unary_float_op Uop_float_floor -> "floor"
  | Enhanced_unary_float_op Uop_float_truncate -> "Ftruncate"
  | Enhanced_unary_float_op Uop_float_abs -> "Fabs"
  | Enhanced_unary_float_op Uop_float_sum -> "Fsum"
  | Enhanced_unary_float_op Uop_float_arithmean -> "Favg"
  | Enhanced_unary_float_op Uop_float_listmin -> "Flist_min"
  | Enhanced_unary_float_op Uop_float_listmax -> "Flist_max"
  | Enhanced_unary_time_op Uop_time_to_scale -> "TimeToScale"
  | Enhanced_unary_time_op Uop_time_from_string -> "TimeFromString"
  | Enhanced_unary_time_op Uop_time_duration_from_string -> "TimeDurationFromString"
  | Enhanced_unary_sql_date_op (Uop_sql_get_date_component part) -> "(SqlGetDateComponent " ^ (sql_date_component_to_string part) ^ ")"
  | Enhanced_unary_sql_date_op Uop_sql_date_from_string -> "SqlDateFromString"
  | Enhanced_unary_sql_date_op Uop_sql_date_interval_from_string -> "SqlDateIntervalFromString"
									    
let foreign_unary_op_of_string s =
  match s with
  | "Fneg" -> Enhanced_unary_float_op Uop_float_neg
  | "Fsqrt" -> Enhanced_unary_float_op Uop_float_sqrt
  | "Fexp" -> Enhanced_unary_float_op Uop_float_exp
  | "Flog" -> Enhanced_unary_float_op Uop_float_log
  | "Flog10" -> Enhanced_unary_float_op Uop_float_log10
  | "Fof_int" -> Enhanced_unary_float_op Uop_float_of_int
  | "Fceil" -> Enhanced_unary_float_op Uop_float_ceil
  | "floor" -> Enhanced_unary_float_op Uop_float_floor
  | "Ftruncate" -> Enhanced_unary_float_op Uop_float_truncate
  | "Fabs" -> Enhanced_unary_float_op Uop_float_abs
  | "Fsum" -> Enhanced_unary_float_op Uop_float_sum
  | "Favg" -> Enhanced_unary_float_op Uop_float_arithmean
  | "Flist_min" -> Enhanced_unary_float_op Uop_float_listmin
  | "Flist_max" -> Enhanced_unary_float_op Uop_float_listmax
  | "TimeToScale" -> Enhanced_unary_time_op Uop_time_to_scale
  | "TimeFromString" -> Enhanced_unary_time_op Uop_time_from_string
  | "TimeDurationFromString" -> Enhanced_unary_time_op Uop_time_duration_from_string
  | "(SqlGetDateComponent DAY)"->  Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_DAY)
  | "(SqlGetDateComponent MONTH)"->  Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_MONTH)
  | "(SqlGetDateComponent YEAR)"->  Enhanced_unary_sql_date_op (Uop_sql_get_date_component Sql_date_YEAR)
  | "SqlDateFromString" -> Enhanced_unary_sql_date_op Uop_sql_date_from_string
  | "SqlDateIntervalFromString" -> Enhanced_unary_sql_date_op Uop_sql_date_interval_from_string

  | _ -> raise Not_found

let string_of_arith_binary_op ba =
  match ba with
  | ArithPlus -> "plus"
  | ArithMinus -> "minus"
  | ArithMult -> "mult"
  | ArithMin -> "min"
  | ArithMax -> "max"
  | ArithDivide -> "divide"
  | ArithRem -> "rem"

let arith_binary_op_of_string s =
  match s with
  | "plus" -> ArithPlus
  | "minus" -> ArithMinus
  | "mult" -> ArithMult
  | "min" -> ArithMin
  | "max" -> ArithMax
  | "divide" -> ArithDivide
  | "rem" -> ArithRem
  | _ -> raise Not_found

let string_of_foreign_binary_op fb =
  match fb with
  | Enhanced_binary_float_op Bop_float_plus -> "float_plus"
  | Enhanced_binary_float_op Bop_float_minus -> "float_minus"
  | Enhanced_binary_float_op Bop_float_mult -> "float_mult"
  | Enhanced_binary_float_op Bop_float_div -> "float_div"
  | Enhanced_binary_float_op Bop_float_pow -> "float_pow"
  | Enhanced_binary_float_op Bop_float_min -> "float_min"
  | Enhanced_binary_float_op Bop_float_max -> "float_max"
  | Enhanced_binary_float_op Bop_float_ne -> "float_ne"
  | Enhanced_binary_float_op Bop_float_lt -> "float_lt"
  | Enhanced_binary_float_op Bop_float_le -> "float_le"
  | Enhanced_binary_float_op Bop_float_gt -> "float_gt"
  | Enhanced_binary_float_op Bop_float_ge -> "float_ge"
  | Enhanced_binary_time_op Bop_time_as -> "time_as"
  | Enhanced_binary_time_op Bop_time_shift -> "time_shift"
  | Enhanced_binary_time_op Bop_time_ne -> "time_ne"
  | Enhanced_binary_time_op Bop_time_lt -> "time_lt"
  | Enhanced_binary_time_op Bop_time_le -> "time_le"
  | Enhanced_binary_time_op Bop_time_gt -> "time_gt"
  | Enhanced_binary_time_op Bop_time_ge -> "time_ge"
  | Enhanced_binary_time_op Bop_time_duration_from_scale -> "time_duration_from_scale"
  | Enhanced_binary_time_op Bop_time_duration_between -> "time_duration_between"
  | Enhanced_binary_sql_date_op Bop_sql_date_plus -> "sql_date_plus"
  | Enhanced_binary_sql_date_op Bop_sql_date_minus -> "sql_date_minus"
  | Enhanced_binary_sql_date_op Bop_sql_date_ne -> "sql_date_ne"
  | Enhanced_binary_sql_date_op Bop_sql_date_lt -> "sql_date_lt"
  | Enhanced_binary_sql_date_op Bop_sql_date_le -> "sql_date_le"
  | Enhanced_binary_sql_date_op Bop_sql_date_gt -> "sql_date_gt"
  | Enhanced_binary_sql_date_op Bop_sql_date_ge -> "sql_date_ge"
  | Enhanced_binary_sql_date_op Bop_sql_date_interval_between -> "sql_date_interval_between"

let foreign_binary_op_of_string fb =
  match fb with
  | "float_plus" -> Enhanced_binary_float_op Bop_float_plus
  | "float_minus" -> Enhanced_binary_float_op Bop_float_minus
  | "float_mult" -> Enhanced_binary_float_op Bop_float_mult
  | "float_div" -> Enhanced_binary_float_op Bop_float_div
  | "float_pow" -> Enhanced_binary_float_op Bop_float_pow
  | "float_min" -> Enhanced_binary_float_op Bop_float_min
  | "float_max" -> Enhanced_binary_float_op Bop_float_max
  | "float_ne" -> Enhanced_binary_float_op Bop_float_ne
  | "float_lt" -> Enhanced_binary_float_op Bop_float_lt
  | "float_le" -> Enhanced_binary_float_op Bop_float_le
  | "float_gt" -> Enhanced_binary_float_op Bop_float_gt
  | "float_ge" -> Enhanced_binary_float_op Bop_float_ge
  | "time_as" -> Enhanced_binary_time_op Bop_time_as
  | "time_shift" -> Enhanced_binary_time_op Bop_time_shift
  | "time_ne" -> Enhanced_binary_time_op Bop_time_ne
  | "time_lt" -> Enhanced_binary_time_op Bop_time_lt
  | "time_le" -> Enhanced_binary_time_op Bop_time_le
  | "time_gt" -> Enhanced_binary_time_op Bop_time_gt
  | "time_ge" -> Enhanced_binary_time_op Bop_time_ge
  | "time_duration_from_scale" -> Enhanced_binary_time_op Bop_time_duration_from_scale
  | "time_duration_between" -> Enhanced_binary_time_op Bop_time_duration_between
  | "sql_date_plus" -> Enhanced_binary_sql_date_op Bop_sql_date_plus
  | "sql_date_ne" -> Enhanced_binary_sql_date_op Bop_sql_date_ne
  | "sql_date_lt" -> Enhanced_binary_sql_date_op Bop_sql_date_lt
  | "sql_date_le" -> Enhanced_binary_sql_date_op Bop_sql_date_le
  | "sql_date_gt" -> Enhanced_binary_sql_date_op Bop_sql_date_gt
  | "sql_date_ge" -> Enhanced_binary_sql_date_op Bop_sql_date_ge
  | "sql_date_interval_between" -> Enhanced_binary_sql_date_op Bop_sql_date_interval_between
  | _ -> raise Not_found

let string_of_binary_op b =
  match b with
  | OpEqual -> "aeq"
  | OpBagUnion -> "aunion"
  | OpRecConcat -> "aconcat"
  | OpRecMerge -> "amergeconcat"
  | OpAnd -> "aand"
  | OpOr -> "aor"
  | OpArithBinary ba -> string_of_arith_binary_op ba
  | OpLt -> "alt"
  | OpLe -> "ale"
  | OpBagDiff -> "aminus"
  | OpBagMin -> "amin"
  | OpBagMax -> "amax"
  | OpContains -> "acontains"
  | OpStringConcat -> "asconcat"
  | OpForeignBinary fb -> string_of_foreign_binary_op (Obj.magic fb)

