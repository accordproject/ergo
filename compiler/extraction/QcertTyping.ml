open BrandRelation
open DateTimeComponent
open ForeignOperatorsTyping
open ForeignTyping
open MathComponent
open MonetaryAmountComponent
open QcertData
open QcertDataTyping
open QcertType
open RSubtype
open RType
open TBrandModel
open UriComponent

(** val coq_DateTimeFormat : brand_relation -> rtype **)

let coq_DateTimeFormat br =
  coq_Foreign enhanced_foreign_type br (Obj.magic Coq_enhancedDateTimeFormat)

(** val coq_DateTime : brand_relation -> rtype **)

let coq_DateTime br =
  coq_Foreign enhanced_foreign_type br (Obj.magic Coq_enhancedDateTime)

(** val coq_DateTimeDuration : brand_relation -> rtype **)

let coq_DateTimeDuration br =
  coq_Foreign enhanced_foreign_type br
    (Obj.magic Coq_enhancedDateTimeDuration)

(** val coq_DateTimePeriod : brand_relation -> rtype **)

let coq_DateTimePeriod br =
  coq_Foreign enhanced_foreign_type br (Obj.magic Coq_enhancedDateTimePeriod)

(** val isDateTimeFormat : brand_model -> rtype -> bool **)

let isDateTimeFormat _ = function
| Foreign_UU2080_ ft ->
  (match Obj.magic ft with
   | Coq_enhancedDateTimeFormat -> true
   | _ -> false)
| _ -> false

(** val isDateTime : brand_model -> rtype -> bool **)

let isDateTime _ = function
| Foreign_UU2080_ ft ->
  (match Obj.magic ft with
   | Coq_enhancedDateTime -> true
   | _ -> false)
| _ -> false

(** val isDateTimeDuration : brand_model -> rtype -> bool **)

let isDateTimeDuration _ = function
| Foreign_UU2080_ ft ->
  (match Obj.magic ft with
   | Coq_enhancedDateTimeDuration -> true
   | _ -> false)
| _ -> false

(** val isDateTimePeriod : brand_model -> rtype -> bool **)

let isDateTimePeriod _ = function
| Foreign_UU2080_ ft ->
  (match Obj.magic ft with
   | Coq_enhancedDateTimePeriod -> true
   | _ -> false)
| _ -> false

(** val isNat : brand_model -> rtype -> bool **)

let isNat _ = function
| Nat_UU2080_ -> true
| _ -> false

(** val isString : brand_model -> rtype -> bool **)

let isString _ = function
| String_UU2080_ -> true
| _ -> false

(** val isFloat : brand_model -> rtype -> bool **)

let isFloat _ = function
| Float_UU2080_ -> true
| _ -> false

(** val tuncoll : brand_model -> rtype -> rtype option **)

let tuncoll _ = function
| Coll_UU2080_ x -> Some x
| _ -> None

(** val uri_unary_op_type_infer :
    brand_model -> uri_unary_op -> rtype -> rtype option **)

let uri_unary_op_type_infer model _ _UU03c4__UU2081_ =
  if isString model _UU03c4__UU2081_
  then Some (coq_String enhanced_foreign_type model.brand_model_relation)
  else None

(** val log_unary_op_type_infer : brand_model -> rtype -> rtype option **)

let log_unary_op_type_infer model _UU03c4__UU2081_ =
  if isString model _UU03c4__UU2081_
  then Some (coq_Unit enhanced_foreign_type model.brand_model_relation)
  else None

(** val math_unary_op_type_infer :
    brand_model -> math_unary_op -> rtype -> rtype option **)

let math_unary_op_type_infer model op _UU03c4__UU2081_ =
  match op with
  | Coq_uop_math_float_of_string ->
    if isString model _UU03c4__UU2081_
    then Some
           (coq_Option enhanced_foreign_type model.brand_model_relation
             (coq_Float enhanced_foreign_type model.brand_model_relation))
    else None
  | _ ->
    if isFloat model _UU03c4__UU2081_
    then Some (coq_Float enhanced_foreign_type model.brand_model_relation)
    else None

(** val date_time_unary_op_type_infer :
    brand_model -> date_time_unary_op -> rtype -> rtype option **)

let date_time_unary_op_type_infer model op _UU03c4__UU2081_ =
  match op with
  | Coq_uop_date_time_get_seconds ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_minutes ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_hours ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_days ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_weeks ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_months ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_quarters ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_get_years ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_format_from_string ->
    if isString model _UU03c4__UU2081_
    then Some (coq_DateTimeFormat model.brand_model_relation)
    else None
  | Coq_uop_date_time_from_string ->
    if isString model _UU03c4__UU2081_
    then Some (coq_DateTime model.brand_model_relation)
    else None
  | Coq_uop_date_time_max ->
    (match tuncoll model _UU03c4__UU2081_ with
     | Some _UU03c4__UU2082_ ->
       if isDateTime model _UU03c4__UU2082_
       then Some (coq_DateTime model.brand_model_relation)
       else None
     | None -> None)
  | Coq_uop_date_time_min ->
    (match tuncoll model _UU03c4__UU2081_ with
     | Some _UU03c4__UU2082_ ->
       if isDateTime model _UU03c4__UU2082_
       then Some (coq_DateTime model.brand_model_relation)
       else None
     | None -> None)
  | Coq_uop_date_time_duration_amount ->
    if isDateTimeDuration model _UU03c4__UU2081_
    then Some (coq_Nat enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_string ->
    if isString model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_seconds ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_minutes ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_hours ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_days ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_duration_from_weeks ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_string ->
    if isString model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_days ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_weeks ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_months ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_quarters ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | Coq_uop_date_time_period_from_years ->
    if isNat model _UU03c4__UU2081_
    then Some (coq_DateTimePeriod model.brand_model_relation)
    else None
  | _ ->
    if isDateTime model _UU03c4__UU2081_
    then Some (coq_DateTime model.brand_model_relation)
    else None

(** val uri_unary_op_type_infer_sub :
    brand_model -> uri_unary_op -> rtype -> (rtype * rtype) option **)

let uri_unary_op_type_infer_sub model _ _UU03c4__UU2081_ =
  enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
    (_UU03c4__UU2081_,
    (coq_String enhanced_foreign_type model.brand_model_relation))
    (coq_String enhanced_foreign_type model.brand_model_relation)

(** val log_unary_op_type_infer_sub :
    brand_model -> rtype -> (rtype * rtype) option **)

let log_unary_op_type_infer_sub model _UU03c4__UU2081_ =
  enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
    (_UU03c4__UU2081_,
    (coq_String enhanced_foreign_type model.brand_model_relation))
    (coq_Unit enhanced_foreign_type model.brand_model_relation)

(** val math_unary_op_type_infer_sub :
    brand_model -> math_unary_op -> rtype -> (rtype * rtype) option **)

let math_unary_op_type_infer_sub model op _UU03c4__UU2081_ =
  match op with
  | Coq_uop_math_float_of_string ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_Option enhanced_foreign_type model.brand_model_relation
        (coq_Float enhanced_foreign_type model.brand_model_relation))
  | _ ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Float enhanced_foreign_type model.brand_model_relation))
      (coq_Float enhanced_foreign_type model.brand_model_relation)

(** val date_time_unary_op_type_infer_sub :
    brand_model -> date_time_unary_op -> rtype -> (rtype * rtype) option **)

let date_time_unary_op_type_infer_sub model op _UU03c4__UU2081_ =
  match op with
  | Coq_uop_date_time_get_seconds ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_minutes ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_hours ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_days ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_weeks ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_months ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_quarters ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_get_years ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_format_from_string ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeFormat model.brand_model_relation)
  | Coq_uop_date_time_from_string ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)
  | Coq_uop_date_time_max ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Coll enhanced_foreign_type model.brand_model_relation
        (coq_DateTime model.brand_model_relation)))
      (coq_DateTime model.brand_model_relation)
  | Coq_uop_date_time_min ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Coll enhanced_foreign_type model.brand_model_relation
        (coq_DateTime model.brand_model_relation)))
      (coq_DateTime model.brand_model_relation)
  | Coq_uop_date_time_duration_amount ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTimeDuration model.brand_model_relation))
      (coq_Nat enhanced_foreign_type model.brand_model_relation)
  | Coq_uop_date_time_duration_from_string ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_duration_from_seconds ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_duration_from_minutes ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_duration_from_hours ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_duration_from_days ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_duration_from_weeks ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | Coq_uop_date_time_period_from_string ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | Coq_uop_date_time_period_from_days ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | Coq_uop_date_time_period_from_weeks ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | Coq_uop_date_time_period_from_months ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | Coq_uop_date_time_period_from_quarters ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | Coq_uop_date_time_period_from_years ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Nat enhanced_foreign_type model.brand_model_relation))
      (coq_DateTimePeriod model.brand_model_relation)
  | _ ->
    enforce_unary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)

(** val enhanced_unary_op_typing_infer :
    brand_model -> enhanced_unary_op -> rtype -> rtype option **)

let enhanced_unary_op_typing_infer model fu _UU03c4_ =
  match fu with
  | Coq_enhanced_unary_uri_op op -> uri_unary_op_type_infer model op _UU03c4_
  | Coq_enhanced_unary_log_op -> log_unary_op_type_infer model _UU03c4_
  | Coq_enhanced_unary_math_op op ->
    math_unary_op_type_infer model op _UU03c4_
  | Coq_enhanced_unary_date_time_op op ->
    date_time_unary_op_type_infer model op _UU03c4_

(** val enhanced_unary_op_typing_infer_sub :
    brand_model -> enhanced_unary_op -> rtype -> (rtype * rtype) option **)

let enhanced_unary_op_typing_infer_sub model fu _UU03c4_ =
  match fu with
  | Coq_enhanced_unary_uri_op op ->
    uri_unary_op_type_infer_sub model op _UU03c4_
  | Coq_enhanced_unary_log_op -> log_unary_op_type_infer_sub model _UU03c4_
  | Coq_enhanced_unary_math_op op ->
    math_unary_op_type_infer_sub model op _UU03c4_
  | Coq_enhanced_unary_date_time_op op ->
    date_time_unary_op_type_infer_sub model op _UU03c4_

(** val math_binary_op_type_infer :
    brand_model -> rtype -> rtype -> rtype option **)

let math_binary_op_type_infer model _UU03c4__UU2081_ _UU03c4__UU2082_ =
  if (&&) (isFloat model _UU03c4__UU2081_) (isFloat model _UU03c4__UU2082_)
  then Some (coq_Float enhanced_foreign_type model.brand_model_relation)
  else None

(** val date_time_binary_op_type_infer :
    brand_model -> date_time_binary_op -> rtype -> rtype -> rtype option **)

let date_time_binary_op_type_infer model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_bop_date_time_format ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTimeFormat model _UU03c4__UU2082_)
    then Some (coq_String enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_bop_date_time_add ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTimeDuration model _UU03c4__UU2082_)
    then Some (coq_DateTime model.brand_model_relation)
    else None
  | Coq_bop_date_time_subtract ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTimeDuration model _UU03c4__UU2082_)
    then Some (coq_DateTime model.brand_model_relation)
    else None
  | Coq_bop_date_time_add_period ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTimePeriod model _UU03c4__UU2082_)
    then Some (coq_DateTime model.brand_model_relation)
    else None
  | Coq_bop_date_time_subtract_period ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTimePeriod model _UU03c4__UU2082_)
    then Some (coq_DateTime model.brand_model_relation)
    else None
  | Coq_bop_date_time_diff ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTime model _UU03c4__UU2082_)
    then Some (coq_DateTimeDuration model.brand_model_relation)
    else None
  | _ ->
    if (&&) (isDateTime model _UU03c4__UU2081_)
         (isDateTime model _UU03c4__UU2082_)
    then Some (coq_Bool enhanced_foreign_type model.brand_model_relation)
    else None

(** val monetary_amount_binary_op_type_infer :
    brand_model -> monetary_amount_binary_op -> rtype -> rtype -> rtype option **)

let monetary_amount_binary_op_type_infer model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_bop_monetary_amount_format ->
    if (&&) (isFloat model _UU03c4__UU2081_) (isString model _UU03c4__UU2082_)
    then Some (coq_String enhanced_foreign_type model.brand_model_relation)
    else None
  | Coq_bop_monetary_code_format ->
    if (&&) (isString model _UU03c4__UU2081_)
         (isString model _UU03c4__UU2082_)
    then Some (coq_String enhanced_foreign_type model.brand_model_relation)
    else None

(** val math_binary_op_type_infer_sub :
    brand_model -> rtype -> rtype -> ((rtype * rtype) * rtype) option **)

let math_binary_op_type_infer_sub model _UU03c4__UU2081_ _UU03c4__UU2082_ =
  enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
    (_UU03c4__UU2081_,
    (coq_Float enhanced_foreign_type model.brand_model_relation))
    (_UU03c4__UU2082_,
    (coq_Float enhanced_foreign_type model.brand_model_relation))
    (coq_Float enhanced_foreign_type model.brand_model_relation)

(** val date_time_binary_op_type_infer_sub :
    brand_model -> date_time_binary_op -> rtype -> rtype ->
    ((rtype * rtype) * rtype) option **)

let date_time_binary_op_type_infer_sub model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_bop_date_time_format ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTimeFormat model.brand_model_relation))
      (coq_String enhanced_foreign_type model.brand_model_relation)
  | Coq_bop_date_time_add ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTimeDuration model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)
  | Coq_bop_date_time_subtract ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTimeDuration model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)
  | Coq_bop_date_time_add_period ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTimePeriod model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)
  | Coq_bop_date_time_subtract_period ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTimePeriod model.brand_model_relation))
      (coq_DateTime model.brand_model_relation)
  | Coq_bop_date_time_diff ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTime model.brand_model_relation))
      (coq_DateTimeDuration model.brand_model_relation)
  | _ ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_, (coq_DateTime model.brand_model_relation))
      (_UU03c4__UU2082_, (coq_DateTime model.brand_model_relation))
      (coq_Bool enhanced_foreign_type model.brand_model_relation)

(** val monetary_amount_binary_op_type_infer_sub :
    brand_model -> monetary_amount_binary_op -> rtype -> rtype ->
    ((rtype * rtype) * rtype) option **)

let monetary_amount_binary_op_type_infer_sub model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_bop_monetary_amount_format ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_Float enhanced_foreign_type model.brand_model_relation))
      (_UU03c4__UU2082_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_String enhanced_foreign_type model.brand_model_relation)
  | Coq_bop_monetary_code_format ->
    enforce_binary_op_schema enhanced_foreign_type model.brand_model_relation
      (_UU03c4__UU2081_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (_UU03c4__UU2082_,
      (coq_String enhanced_foreign_type model.brand_model_relation))
      (coq_String enhanced_foreign_type model.brand_model_relation)

(** val enhanced_binary_op_typing_infer :
    brand_model -> enhanced_binary_op -> rtype -> rtype -> rtype option **)

let enhanced_binary_op_typing_infer model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_enhanced_binary_math_op ->
    math_binary_op_type_infer model _UU03c4__UU2081_ _UU03c4__UU2082_
  | Coq_enhanced_binary_date_time_op fb ->
    date_time_binary_op_type_infer model fb _UU03c4__UU2081_ _UU03c4__UU2082_
  | Coq_enhanced_binary_monetary_amount_op fb ->
    monetary_amount_binary_op_type_infer model fb _UU03c4__UU2081_
      _UU03c4__UU2082_

(** val enhanced_binary_op_typing_infer_sub :
    brand_model -> enhanced_binary_op -> rtype -> rtype ->
    ((rtype * rtype) * rtype) option **)

let enhanced_binary_op_typing_infer_sub model op _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match op with
  | Coq_enhanced_binary_math_op ->
    math_binary_op_type_infer_sub model _UU03c4__UU2081_ _UU03c4__UU2082_
  | Coq_enhanced_binary_date_time_op fb ->
    date_time_binary_op_type_infer_sub model fb _UU03c4__UU2081_
      _UU03c4__UU2082_
  | Coq_enhanced_binary_monetary_amount_op fb ->
    monetary_amount_binary_op_type_infer_sub model fb _UU03c4__UU2081_
      _UU03c4__UU2082_

(** val enhanced_foreign_operators_typing :
    brand_model -> foreign_operators_typing **)

let enhanced_foreign_operators_typing model =
  { foreign_operators_typing_unary_infer =
    (Obj.magic enhanced_unary_op_typing_infer model);
    foreign_operators_typing_unary_infer_sub =
    (Obj.magic enhanced_unary_op_typing_infer_sub model);
    foreign_operators_typing_binary_infer =
    (Obj.magic enhanced_binary_op_typing_infer model);
    foreign_operators_typing_binary_infer_sub =
    (Obj.magic enhanced_binary_op_typing_infer_sub model) }

(** val enhanced_foreign_typing : brand_model -> foreign_typing **)

let enhanced_foreign_typing model =
  { foreign_typing_data = enhanced_foreign_data_typing;
    foreign_typing_operators = (enhanced_foreign_operators_typing model) }
