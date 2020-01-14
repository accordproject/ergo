open Apply
open BrandRelation
open CoqLibAdd
open Datatypes
open DateTimeComponent
open EJson
open EJsonRuntimeOperators
open EmitUtil
open Encode
open EquivDec
open ForeignData
open ForeignEJson
open ForeignEJsonRuntime
open List0
open LogComponent
open MathComponent
open MonetaryAmountComponent
open QcertData
open String0
open ToString
open UriComponent

let __ = let rec f _ = Obj.repr f in Obj.repr f

type enhanced_ejson = enhanced_data

(** val enhanced_foreign_ejson_obligation_3 :
    enhanced_ejson -> enhanced_ejson **)

let enhanced_foreign_ejson_obligation_3 a =
  a

(** val enhanced_foreign_ejson_obligation_1 : enhanced_ejson coq_EqDec **)

let enhanced_foreign_ejson_obligation_1 x y =
  match x with
  | Coq_enhanceddateTimeformat d ->
    (match y with
     | Coq_enhanceddateTimeformat d0 ->
       equiv_dec (Obj.magic date_time_format_foreign_data.foreign_data_dec) d
         d0
     | _ -> false)
  | Coq_enhanceddateTime d ->
    (match y with
     | Coq_enhanceddateTime d0 ->
       equiv_dec (Obj.magic date_time_foreign_data.foreign_data_dec) d d0
     | _ -> false)
  | Coq_enhanceddateTimeduration d ->
    (match y with
     | Coq_enhanceddateTimeduration d0 ->
       equiv_dec (Obj.magic date_time_duration_foreign_data.foreign_data_dec)
         d d0
     | _ -> false)
  | Coq_enhanceddateTimeperiod d ->
    (match y with
     | Coq_enhanceddateTimeperiod d0 ->
       equiv_dec (Obj.magic date_time_period_foreign_data.foreign_data_dec) d
         d0
     | _ -> false)

(** val enhanced_foreign_ejson_obligation_6 : enhanced_ejson coq_ToString **)

let enhanced_foreign_ejson_obligation_6 = function
| Coq_enhanceddateTimeformat d ->
  toString (Obj.magic date_time_format_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTime d ->
  toString (Obj.magic date_time_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTimeduration d ->
  toString (Obj.magic date_time_duration_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTimeperiod d ->
  toString (Obj.magic date_time_period_foreign_data.foreign_data_tostring) d

(** val enhanced_foreign_ejson : enhanced_ejson foreign_ejson **)

let enhanced_foreign_ejson =
  { foreign_ejson_dec = enhanced_foreign_ejson_obligation_1;
    foreign_ejson_normalize = enhanced_foreign_ejson_obligation_3;
    foreign_ejson_tostring = enhanced_foreign_ejson_obligation_6 }

type enhanced_foreign_ejson_runtime_op =
| Coq_enhanced_ejson_uri of ejson_uri_runtime_op
| Coq_enhanced_ejson_log
| Coq_enhanced_ejson_math of ejson_math_runtime_op
| Coq_enhanced_ejson_date_time of ejson_date_time_runtime_op
| Coq_enhanced_ejson_monetary_amount of ejson_monetary_amount_runtime_op

(** val enhanced_foreign_ejson_runtime_op_tostring :
    enhanced_foreign_ejson_runtime_op -> char list **)

let enhanced_foreign_ejson_runtime_op_tostring = function
| Coq_enhanced_ejson_uri sop -> ejson_uri_runtime_op_tostring sop
| Coq_enhanced_ejson_log -> ejson_log_runtime_op_tostring __
| Coq_enhanced_ejson_math sop -> ejson_math_runtime_op_tostring sop
| Coq_enhanced_ejson_date_time sop -> ejson_date_time_runtime_op_tostring sop
| Coq_enhanced_ejson_monetary_amount sop ->
  ejson_monetary_amount_runtime_op_tostring sop

(** val enhanced_foreign_ejson_runtime_op_fromstring :
    char list -> enhanced_foreign_ejson_runtime_op option **)

let enhanced_foreign_ejson_runtime_op_fromstring s =
  match ejson_uri_runtime_op_fromstring s with
  | Some op -> Some (Coq_enhanced_ejson_uri op)
  | None ->
    (match ejson_log_runtime_op_fromstring s with
     | Some _ -> Some Coq_enhanced_ejson_log
     | None ->
       (match ejson_math_runtime_op_fromstring s with
        | Some op -> Some (Coq_enhanced_ejson_math op)
        | None ->
          (match ejson_date_time_runtime_op_fromstring s with
           | Some op -> Some (Coq_enhanced_ejson_date_time op)
           | None ->
             (match ejson_monetary_amount_runtime_op_fromstring s with
              | Some op -> Some (Coq_enhanced_ejson_monetary_amount op)
              | None -> None))))

(** val enhanced_ejson_uri_runtime_op_interp :
    ejson_uri_runtime_op -> enhanced_ejson ejson list -> enhanced_ejson ejson
    option **)

let enhanced_ejson_uri_runtime_op_interp op dl =
  match op with
  | EJsonRuntimeUriEncode ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejstring ((fun x -> Uri_component.encode x) s))
      | _ -> None) dl
  | EJsonRuntimeUriDecode ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejstring ((fun x -> Uri_component.decode x) s))
      | _ -> None) dl

(** val onjstringunit :
    (char list -> unit) -> enhanced_ejson ejson -> enhanced_ejson ejson option **)

let onjstringunit f = function
| Coq_ejstring s -> if unit_eqdec (f s) () then Some Coq_ejnull else None
| _ -> None

(** val enhanced_ejson_log_runtime_op_interp :
    enhanced_ejson ejson list -> enhanced_ejson ejson option **)

let enhanced_ejson_log_runtime_op_interp dl =
  apply_unary (onjstringunit (fun x -> Logger.log_string x)) dl

(** val enhanced_ejson_math_runtime_op_interp :
    ejson_math_runtime_op -> enhanced_ejson ejson list -> enhanced_ejson
    ejson option **)

let enhanced_ejson_math_runtime_op_interp op dl =
  match op with
  | EJsonRuntimeFloatOfString ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        (match (fun x -> Util.ergo_float_of_string x) s with
         | Some f ->
           Some (Coq_ejobject ((('$'::('l'::('e'::('f'::('t'::[]))))),
             (Coq_ejnumber f)) :: []))
         | None ->
           Some (Coq_ejobject ((('$'::('r'::('i'::('g'::('h'::('t'::[])))))),
             Coq_ejnull) :: [])))
      | _ -> None) dl
  | EJsonRuntimeAcos ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> acos x) f))
      | _ -> None) dl
  | EJsonRuntimeAsin ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> asin x) f))
      | _ -> None) dl
  | EJsonRuntimeAtan ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> atan x) f))
      | _ -> None) dl
  | EJsonRuntimeAtan2 ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejnumber f1 ->
        (match d2 with
         | Coq_ejnumber f2 ->
           Some (Coq_ejnumber ((fun x y -> atan2 x y) f1 f2))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeCos ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> cos x) f))
      | _ -> None) dl
  | EJsonRuntimeCosh ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> cosh x) f))
      | _ -> None) dl
  | EJsonRuntimeSin ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> sin x) f))
      | _ -> None) dl
  | EJsonRuntimeSinh ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> sinh x) f))
      | _ -> None) dl
  | EJsonRuntimeTan ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> tan x) f))
      | _ -> None) dl
  | EJsonRuntimeTanh ->
    apply_unary (fun d ->
      match d with
      | Coq_ejnumber f -> Some (Coq_ejnumber ((fun x -> tanh x) f))
      | _ -> None) dl

(** val ejson_dates :
    enhanced_data ejson list -> coq_DATE_TIME list option **)

let rec ejson_dates = function
| [] -> Some []
| e :: d' ->
  (match e with
   | Coq_ejforeign y ->
     (match y with
      | Coq_enhanceddateTime d0 ->
        (match ejson_dates d' with
         | Some s' -> Some (d0 :: s')
         | None -> None)
      | _ -> None)
   | _ -> None)

(** val enhanced_ejson_date_time_runtime_op_interp :
    ejson_date_time_runtime_op -> enhanced_data ejson list -> enhanced_data
    ejson option **)

let enhanced_ejson_date_time_runtime_op_interp op dl =
  match op with
  | EJsonRuntimeDateTimeGetSeconds ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint
             ((fun x -> Date_time_component.get_seconds x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetMinutes ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint
             ((fun x -> Date_time_component.get_minutes x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetHours ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint ((fun x -> Date_time_component.get_hours x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetDays ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint ((fun x -> Date_time_component.get_days x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetWeeks ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint ((fun x -> Date_time_component.get_weeks x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetMonths ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint
             ((fun x -> Date_time_component.get_months x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetQuarters ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint
             ((fun x -> Date_time_component.get_quarters x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeGetYears ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejbigint ((fun x -> Date_time_component.get_years x) d0))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeStartOfDay ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.start_of_day x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeStartOfWeek ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.start_of_week x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeStartOfMonth ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.start_of_month x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeStartOfQuarter ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.start_of_quarter x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeStartOfYear ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.start_of_year x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeEndOfDay ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.end_of_day x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeEndOfWeek ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.end_of_week x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeEndOfMonth ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.end_of_month x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeEndOfQuarter ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.end_of_quarter x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeEndOfYear ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.end_of_year x) d0)))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeFormatFromString ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeformat
          ((fun x -> Date_time_component.format_from_string (Util.string_of_char_list x))
            s)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeFromString ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejforeign (Coq_enhanceddateTime
          ((fun x -> Date_time_component.from_string (Util.string_of_char_list x))
            s)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeMax ->
    apply_unary (fun d ->
      match d with
      | Coq_ejarray jl ->
        (match ejson_dates jl with
         | Some dl0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.max x) dl0)))
         | None -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeMin ->
    apply_unary (fun d ->
      match d with
      | Coq_ejarray jl ->
        (match ejson_dates jl with
         | Some dl0 ->
           Some (Coq_ejforeign (Coq_enhanceddateTime
             ((fun x -> Date_time_component.min x) dl0)))
         | None -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationAmount ->
    apply_unary (fun d ->
      match d with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTimeduration fd ->
           Some (Coq_ejbigint
             ((fun x -> Date_time_component.duration_amount x) fd))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromString ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_string (Util.string_of_char_list x))
            s)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromString ->
    apply_unary (fun d ->
      match d with
      | Coq_ejstring s ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_string (Util.string_of_char_list x))
            s)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromSeconds ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_seconds x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromMinutes ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_minutes x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromHours ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_hours x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromDays ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_days x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeDurationFromWeeks ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeduration
          ((fun x -> Date_time_component.duration_from_weeks x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromDays ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_days x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromWeeks ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_weeks x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromMonths ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_months x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromQuarters ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_quarters x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimePeriodFromYears ->
    apply_unary (fun d ->
      match d with
      | Coq_ejbigint n ->
        Some (Coq_ejforeign (Coq_enhanceddateTimeperiod
          ((fun x -> Date_time_component.period_from_years x) n)))
      | _ -> None) dl
  | EJsonRuntimeDateTimeFormat ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTimeformat f ->
                 Some (Coq_ejstring
                   ((fun x f -> Util.char_list_of_string (Date_time_component.to_string_format x f))
                     d f))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeAdd ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTimeduration du ->
                 Some (Coq_ejforeign (Coq_enhanceddateTime
                   ((fun x y -> Date_time_component.add x y) d du)))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeSubtract ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTimeduration du ->
                 Some (Coq_ejforeign (Coq_enhanceddateTime
                   ((fun x y ->  Date_time_component.subtract x y) d du)))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeAddPeriod ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTimeperiod p ->
                 Some (Coq_ejforeign (Coq_enhanceddateTime
                   ((fun x y -> Date_time_component.add_period x y) d p)))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeSubtractPeriod ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTimeperiod p ->
                 Some (Coq_ejforeign (Coq_enhanceddateTime
                   ((fun x y ->  Date_time_component.subtract_period x y) d p)))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeIsSame ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d3 ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTime d4 ->
                 Some (Coq_ejbool
                   ((fun x y -> Date_time_component.eq x y) d3 d4))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeIsBefore ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d3 ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTime d4 ->
                 Some (Coq_ejbool
                   ((fun x y -> Date_time_component.is_before x y) d3 d4))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeIsAfter ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d3 ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTime d4 ->
                 Some (Coq_ejbool
                   ((fun x y -> Date_time_component.is_after x y) d3 d4))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeDateTimeDiff ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejforeign y ->
        (match y with
         | Coq_enhanceddateTime d3 ->
           (match d2 with
            | Coq_ejforeign e ->
              (match e with
               | Coq_enhanceddateTime d4 ->
                 Some (Coq_ejforeign (Coq_enhanceddateTimeduration
                   ((fun x y -> Date_time_component.diff x y) d3 d4)))
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None) dl

(** val enhanced_ejson_monetary_amount_runtime_op_interp :
    ejson_monetary_amount_runtime_op -> enhanced_ejson ejson list ->
    enhanced_ejson ejson option **)

let enhanced_ejson_monetary_amount_runtime_op_interp op dl =
  match op with
  | EJsonRuntimeMonetaryAmountFormat ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejnumber f1 ->
        (match d2 with
         | Coq_ejstring s2 ->
           Some (Coq_ejstring
             ((fun x1 f -> Util.char_list_of_string (MonetaryAmount.amount_to_string_format x1 (Util.string_of_char_list f)))
               f1 s2))
         | _ -> None)
      | _ -> None) dl
  | EJsonRuntimeMonetaryCodeFormat ->
    apply_binary (fun d1 d2 ->
      match d1 with
      | Coq_ejstring s1 ->
        (match d2 with
         | Coq_ejstring s2 ->
           Some (Coq_ejstring
             ((fun x1 f -> Util.char_list_of_string (MonetaryAmount.code_to_string_format (Util.string_of_char_list x1) (Util.string_of_char_list f)))
               s1 s2))
         | _ -> None)
      | _ -> None) dl

(** val enhanced_foreign_ejson_runtime_op_interp :
    enhanced_foreign_ejson_runtime_op -> enhanced_ejson ejson list ->
    enhanced_ejson ejson option **)

let enhanced_foreign_ejson_runtime_op_interp = function
| Coq_enhanced_ejson_uri sop -> enhanced_ejson_uri_runtime_op_interp sop
| Coq_enhanced_ejson_log -> enhanced_ejson_log_runtime_op_interp
| Coq_enhanced_ejson_math sop -> enhanced_ejson_math_runtime_op_interp sop
| Coq_enhanced_ejson_date_time sop ->
  enhanced_ejson_date_time_runtime_op_interp sop
| Coq_enhanced_ejson_monetary_amount sop ->
  enhanced_ejson_monetary_amount_runtime_op_interp sop

(** val ejsonEnumToString : brands -> enhanced_ejson ejson -> char list **)

let rec ejsonEnumToString b = function
| Coq_ejobject l ->
  (match l with
   | [] ->
     '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[])))))))))))
   | p :: l0 ->
     let (s1, j0) = p in
     (match l0 with
      | [] ->
        if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
        then (match j0 with
              | Coq_ejstring s ->
                append ('~'::[])
                  (append (toString coq_ToString_brands b)
                    (append ('.'::[]) (stringToString s)))
              | _ ->
                '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[]))))))))))))
        else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
             then ejsonEnumToString b j0
             else '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[])))))))))))
      | _ :: _ ->
        '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[])))))))))))))
| _ ->
  '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[])))))))))))

(** val ejsonLeftToString : char list -> char list **)

let ejsonLeftToString j =
  string_bracket ('L'::('e'::('f'::('t'::('('::[]))))) j (')'::[])

(** val ejsonRightToString : char list -> char list **)

let ejsonRightToString j =
  string_bracket ('R'::('i'::('g'::('h'::('t'::('('::[])))))) j (')'::[])

(** val ejsonArrayToString : char list list -> char list **)

let ejsonArrayToString jl =
  string_bracket ('['::[]) (concat (','::(' '::[])) jl) (']'::[])

(** val ejsonObjectToString : (char list * char list) list -> char list **)

let ejsonObjectToString jl =
  string_bracket ('{'::[])
    (concat (','::[])
      (map (fun xy ->
        append (stringToString (key_decode (fst xy)))
          (append (':'::[]) (snd xy))) jl)) ('}'::[])

(** val ejsonToString : enhanced_ejson ejson -> char list **)

let rec ejsonToString = function
| Coq_ejnull -> 'u'::('n'::('i'::('t'::[])))
| Coq_ejnumber n -> toString coq_ToString_float n
| Coq_ejbigint n -> toString coq_ToString_Z n
| Coq_ejbool b -> toString coq_ToString_bool b
| Coq_ejstring s -> string_bracket ('"'::[]) (stringToString s) ('"'::[])
| Coq_ejarray l -> ejsonArrayToString (map ejsonToString l)
| Coq_ejobject r ->
  (match r with
   | [] ->
     ejsonObjectToString
       (map (fun xy -> ((fst xy), (ejsonToString (snd xy)))) r)
   | p :: l ->
     let (s1, j') = p in
     (match j' with
      | Coq_ejarray j1 ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then ejsonLeftToString (ejsonToString j')
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then ejsonRightToString (ejsonToString j')
                else ejsonObjectToString ((s1,
                       (defaultEJsonToString enhanced_foreign_ejson j')) :: [])
         | p0 :: l0 ->
           let (s2, j2) = p0 in
           (match l0 with
            | [] ->
              if string_dec s1 ('$'::('c'::('l'::('a'::('s'::('s'::[]))))))
              then if string_dec s2 ('$'::('d'::('a'::('t'::('a'::[])))))
                   then (match ejson_brands j1 with
                         | Some br ->
                           (match j2 with
                            | Coq_ejobject l1 ->
                              (match l1 with
                               | [] ->
                                 '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[])))))))))))))
                               | p1 :: l2 ->
                                 let (s3, j'0) = p1 in
                                 (match j'0 with
                                  | Coq_ejarray j3 ->
                                    (match l2 with
                                     | [] ->
                                       if string_dec s3
                                            ('$'::('l'::('e'::('f'::('t'::[])))))
                                       then ejsonEnumToString br j'0
                                       else if string_dec s3
                                                 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                                            then ejsonEnumToString br j'0
                                            else append ('~'::[])
                                                   (append
                                                     (toString
                                                       coq_ToString_brands br)
                                                     (ejsonObjectToString
                                                       ((s3,
                                                       (defaultEJsonToString
                                                         enhanced_foreign_ejson
                                                         j'0)) :: [])))
                                     | p2 :: l3 ->
                                       let (s4, j4) = p2 in
                                       (match l3 with
                                        | [] ->
                                          if string_dec s3
                                               ('$'::('c'::('l'::('a'::('s'::('s'::[]))))))
                                          then if string_dec s4
                                                    ('$'::('d'::('a'::('t'::('a'::[])))))
                                               then (match ejson_brands j3 with
                                                     | Some _ ->
                                                       '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[])))))))))))))
                                                     | None ->
                                                       append ('~'::[])
                                                         (append
                                                           (toString
                                                             coq_ToString_brands
                                                             br)
                                                           (ejsonObjectToString
                                                             ((s3,
                                                             (ejsonArrayToString
                                                               (map
                                                                 ejsonToString
                                                                 j3))) :: ((s4,
                                                             (ejsonToString
                                                               j4)) :: [])))))
                                               else append ('~'::[])
                                                      (append
                                                        (toString
                                                          coq_ToString_brands
                                                          br)
                                                        (ejsonObjectToString
                                                          ((s3,
                                                          (ejsonArrayToString
                                                            (map
                                                              ejsonToString
                                                              j3))) :: ((s4,
                                                          (ejsonToString j4)) :: []))))
                                          else append ('~'::[])
                                                 (append
                                                   (toString
                                                     coq_ToString_brands br)
                                                   (ejsonObjectToString ((s3,
                                                     (ejsonArrayToString
                                                       (map ejsonToString j3))) :: ((s4,
                                                     (ejsonToString j4)) :: []))))
                                        | _ :: _ ->
                                          '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[])))))))))))))))
                                  | Coq_ejobject _ ->
                                    (match l2 with
                                     | [] ->
                                       if string_dec s3
                                            ('$'::('l'::('e'::('f'::('t'::[])))))
                                       then ejsonEnumToString br j'0
                                       else if string_dec s3
                                                 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                                            then ejsonEnumToString br j'0
                                            else append ('~'::[])
                                                   (append
                                                     (toString
                                                       coq_ToString_brands br)
                                                     (ejsonObjectToString
                                                       ((s3,
                                                       (defaultEJsonToString
                                                         enhanced_foreign_ejson
                                                         j'0)) :: [])))
                                     | _ :: _ ->
                                       '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[]))))))))))))))
                                  | _ ->
                                    (match l2 with
                                     | [] ->
                                       if string_dec s3
                                            ('$'::('l'::('e'::('f'::('t'::[])))))
                                       then ejsonEnumToString br j'0
                                       else if string_dec s3
                                                 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                                            then ejsonEnumToString br j'0
                                            else append ('~'::[])
                                                   (append
                                                     (toString
                                                       coq_ToString_brands br)
                                                     (ejsonObjectToString
                                                       ((s3,
                                                       (defaultEJsonToString
                                                         enhanced_foreign_ejson
                                                         j'0)) :: [])))
                                     | _ :: _ ->
                                       '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[]))))))))))))))))
                            | _ ->
                              '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[]))))))))))))))
                         | None ->
                           ejsonObjectToString ((s1,
                             (ejsonArrayToString (map ejsonToString j1))) :: ((s2,
                             (ejsonToString j2)) :: [])))
                   else ejsonObjectToString ((s1,
                          (ejsonArrayToString (map ejsonToString j1))) :: ((s2,
                          (ejsonToString j2)) :: []))
              else ejsonObjectToString ((s1,
                     (ejsonArrayToString (map ejsonToString j1))) :: ((s2,
                     (ejsonToString j2)) :: []))
            | _ :: _ ->
              ejsonObjectToString
                (map (fun xy -> ((fst xy), (ejsonToString (snd xy)))) r)))
      | Coq_ejobject _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then ejsonLeftToString (ejsonToString j')
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then ejsonRightToString (ejsonToString j')
                else ejsonObjectToString ((s1,
                       (defaultEJsonToString enhanced_foreign_ejson j')) :: [])
         | _ :: _ ->
           ejsonObjectToString
             (map (fun xy -> ((fst xy), (ejsonToString (snd xy)))) r))
      | _ ->
        (match l with
         | [] ->
           if string_dec s1 ('$'::('l'::('e'::('f'::('t'::[])))))
           then ejsonLeftToString (ejsonToString j')
           else if string_dec s1 ('$'::('r'::('i'::('g'::('h'::('t'::[]))))))
                then ejsonRightToString (ejsonToString j')
                else ejsonObjectToString ((s1,
                       (defaultEJsonToString enhanced_foreign_ejson j')) :: [])
         | _ :: _ ->
           ejsonObjectToString
             (map (fun xy -> ((fst xy), (ejsonToString (snd xy)))) r))))
| Coq_ejforeign fd ->
  toString enhanced_foreign_ejson.foreign_ejson_tostring fd

(** val ejsonToText : enhanced_ejson ejson -> char list **)

let ejsonToText =
  ejsonToString

(** val enhanced_foreign_ejson_runtime_obligation_1 :
    enhanced_foreign_ejson_runtime_op coq_EqDec **)

let enhanced_foreign_ejson_runtime_obligation_1 x y =
  match x with
  | Coq_enhanced_ejson_uri x0 ->
    (match y with
     | Coq_enhanced_ejson_uri e0 ->
       (match x0 with
        | EJsonRuntimeUriEncode ->
          (match e0 with
           | EJsonRuntimeUriEncode -> true
           | EJsonRuntimeUriDecode -> false)
        | EJsonRuntimeUriDecode ->
          (match e0 with
           | EJsonRuntimeUriEncode -> false
           | EJsonRuntimeUriDecode -> true))
     | _ -> false)
  | Coq_enhanced_ejson_log ->
    (match y with
     | Coq_enhanced_ejson_log -> true
     | _ -> false)
  | Coq_enhanced_ejson_math x0 ->
    (match y with
     | Coq_enhanced_ejson_math e0 ->
       (match x0 with
        | EJsonRuntimeFloatOfString ->
          (match e0 with
           | EJsonRuntimeFloatOfString -> true
           | _ -> false)
        | EJsonRuntimeAcos ->
          (match e0 with
           | EJsonRuntimeAcos -> true
           | _ -> false)
        | EJsonRuntimeAsin ->
          (match e0 with
           | EJsonRuntimeAsin -> true
           | _ -> false)
        | EJsonRuntimeAtan ->
          (match e0 with
           | EJsonRuntimeAtan -> true
           | _ -> false)
        | EJsonRuntimeAtan2 ->
          (match e0 with
           | EJsonRuntimeAtan2 -> true
           | _ -> false)
        | EJsonRuntimeCos ->
          (match e0 with
           | EJsonRuntimeCos -> true
           | _ -> false)
        | EJsonRuntimeCosh ->
          (match e0 with
           | EJsonRuntimeCosh -> true
           | _ -> false)
        | EJsonRuntimeSin ->
          (match e0 with
           | EJsonRuntimeSin -> true
           | _ -> false)
        | EJsonRuntimeSinh ->
          (match e0 with
           | EJsonRuntimeSinh -> true
           | _ -> false)
        | EJsonRuntimeTan ->
          (match e0 with
           | EJsonRuntimeTan -> true
           | _ -> false)
        | EJsonRuntimeTanh ->
          (match e0 with
           | EJsonRuntimeTanh -> true
           | _ -> false))
     | _ -> false)
  | Coq_enhanced_ejson_date_time x0 ->
    (match y with
     | Coq_enhanced_ejson_date_time e0 ->
       (match x0 with
        | EJsonRuntimeDateTimeGetSeconds ->
          (match e0 with
           | EJsonRuntimeDateTimeGetSeconds -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetMinutes ->
          (match e0 with
           | EJsonRuntimeDateTimeGetMinutes -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetHours ->
          (match e0 with
           | EJsonRuntimeDateTimeGetHours -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetDays ->
          (match e0 with
           | EJsonRuntimeDateTimeGetDays -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetWeeks ->
          (match e0 with
           | EJsonRuntimeDateTimeGetWeeks -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetMonths ->
          (match e0 with
           | EJsonRuntimeDateTimeGetMonths -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetQuarters ->
          (match e0 with
           | EJsonRuntimeDateTimeGetQuarters -> true
           | _ -> false)
        | EJsonRuntimeDateTimeGetYears ->
          (match e0 with
           | EJsonRuntimeDateTimeGetYears -> true
           | _ -> false)
        | EJsonRuntimeDateTimeStartOfDay ->
          (match e0 with
           | EJsonRuntimeDateTimeStartOfDay -> true
           | _ -> false)
        | EJsonRuntimeDateTimeStartOfWeek ->
          (match e0 with
           | EJsonRuntimeDateTimeStartOfWeek -> true
           | _ -> false)
        | EJsonRuntimeDateTimeStartOfMonth ->
          (match e0 with
           | EJsonRuntimeDateTimeStartOfMonth -> true
           | _ -> false)
        | EJsonRuntimeDateTimeStartOfQuarter ->
          (match e0 with
           | EJsonRuntimeDateTimeStartOfQuarter -> true
           | _ -> false)
        | EJsonRuntimeDateTimeStartOfYear ->
          (match e0 with
           | EJsonRuntimeDateTimeStartOfYear -> true
           | _ -> false)
        | EJsonRuntimeDateTimeEndOfDay ->
          (match e0 with
           | EJsonRuntimeDateTimeEndOfDay -> true
           | _ -> false)
        | EJsonRuntimeDateTimeEndOfWeek ->
          (match e0 with
           | EJsonRuntimeDateTimeEndOfWeek -> true
           | _ -> false)
        | EJsonRuntimeDateTimeEndOfMonth ->
          (match e0 with
           | EJsonRuntimeDateTimeEndOfMonth -> true
           | _ -> false)
        | EJsonRuntimeDateTimeEndOfQuarter ->
          (match e0 with
           | EJsonRuntimeDateTimeEndOfQuarter -> true
           | _ -> false)
        | EJsonRuntimeDateTimeEndOfYear ->
          (match e0 with
           | EJsonRuntimeDateTimeEndOfYear -> true
           | _ -> false)
        | EJsonRuntimeDateTimeFormatFromString ->
          (match e0 with
           | EJsonRuntimeDateTimeFormatFromString -> true
           | _ -> false)
        | EJsonRuntimeDateTimeFromString ->
          (match e0 with
           | EJsonRuntimeDateTimeFromString -> true
           | _ -> false)
        | EJsonRuntimeDateTimeMax ->
          (match e0 with
           | EJsonRuntimeDateTimeMax -> true
           | _ -> false)
        | EJsonRuntimeDateTimeMin ->
          (match e0 with
           | EJsonRuntimeDateTimeMin -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationAmount ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationAmount -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromString ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromString -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromString ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromString -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromSeconds ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromSeconds -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromMinutes ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromMinutes -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromHours ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromHours -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromDays ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromDays -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDurationFromWeeks ->
          (match e0 with
           | EJsonRuntimeDateTimeDurationFromWeeks -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromDays ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromDays -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromWeeks ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromWeeks -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromMonths ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromMonths -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromQuarters ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromQuarters -> true
           | _ -> false)
        | EJsonRuntimeDateTimePeriodFromYears ->
          (match e0 with
           | EJsonRuntimeDateTimePeriodFromYears -> true
           | _ -> false)
        | EJsonRuntimeDateTimeFormat ->
          (match e0 with
           | EJsonRuntimeDateTimeFormat -> true
           | _ -> false)
        | EJsonRuntimeDateTimeAdd ->
          (match e0 with
           | EJsonRuntimeDateTimeAdd -> true
           | _ -> false)
        | EJsonRuntimeDateTimeSubtract ->
          (match e0 with
           | EJsonRuntimeDateTimeSubtract -> true
           | _ -> false)
        | EJsonRuntimeDateTimeAddPeriod ->
          (match e0 with
           | EJsonRuntimeDateTimeAddPeriod -> true
           | _ -> false)
        | EJsonRuntimeDateTimeSubtractPeriod ->
          (match e0 with
           | EJsonRuntimeDateTimeSubtractPeriod -> true
           | _ -> false)
        | EJsonRuntimeDateTimeIsSame ->
          (match e0 with
           | EJsonRuntimeDateTimeIsSame -> true
           | _ -> false)
        | EJsonRuntimeDateTimeIsBefore ->
          (match e0 with
           | EJsonRuntimeDateTimeIsBefore -> true
           | _ -> false)
        | EJsonRuntimeDateTimeIsAfter ->
          (match e0 with
           | EJsonRuntimeDateTimeIsAfter -> true
           | _ -> false)
        | EJsonRuntimeDateTimeDiff ->
          (match e0 with
           | EJsonRuntimeDateTimeDiff -> true
           | _ -> false))
     | _ -> false)
  | Coq_enhanced_ejson_monetary_amount x0 ->
    (match y with
     | Coq_enhanced_ejson_monetary_amount e0 ->
       (match x0 with
        | EJsonRuntimeMonetaryAmountFormat ->
          (match e0 with
           | EJsonRuntimeMonetaryAmountFormat -> true
           | EJsonRuntimeMonetaryCodeFormat -> false)
        | EJsonRuntimeMonetaryCodeFormat ->
          (match e0 with
           | EJsonRuntimeMonetaryAmountFormat -> false
           | EJsonRuntimeMonetaryCodeFormat -> true))
     | _ -> false)

(** val enhanced_foreign_ejson_runtime_obligation_2 :
    enhanced_foreign_ejson_runtime_op coq_ToString **)

let enhanced_foreign_ejson_runtime_obligation_2 =
  enhanced_foreign_ejson_runtime_op_tostring

(** val enhanced_foreign_ejson_runtime_obligation_3 :
    enhanced_foreign_ejson_runtime_op -> enhanced_ejson ejson list ->
    enhanced_ejson ejson option **)

let enhanced_foreign_ejson_runtime_obligation_3 =
  enhanced_foreign_ejson_runtime_op_interp

(** val enhanced_foreign_ejson_runtime_obligation_4 :
    enhanced_ejson ejson -> char list **)

let enhanced_foreign_ejson_runtime_obligation_4 =
  ejsonToString

(** val enhanced_foreign_ejson_runtime_obligation_5 :
    char list -> enhanced_foreign_ejson_runtime_op option **)

let enhanced_foreign_ejson_runtime_obligation_5 =
  enhanced_foreign_ejson_runtime_op_fromstring

(** val enhanced_foreign_ejson_runtime_obligation_6 :
    enhanced_ejson ejson -> char list **)

let enhanced_foreign_ejson_runtime_obligation_6 =
  ejsonToText

(** val enhanced_foreign_ejson_runtime :
    (enhanced_foreign_ejson_runtime_op, enhanced_ejson) foreign_ejson_runtime **)

let enhanced_foreign_ejson_runtime =
  { foreign_ejson_runtime_op_dec =
    enhanced_foreign_ejson_runtime_obligation_1;
    foreign_ejson_runtime_op_tostring =
    enhanced_foreign_ejson_runtime_obligation_2;
    foreign_ejson_runtime_op_interp =
    enhanced_foreign_ejson_runtime_obligation_3;
    foreign_ejson_runtime_tostring =
    enhanced_foreign_ejson_runtime_obligation_4;
    foreign_ejson_runtime_fromstring =
    enhanced_foreign_ejson_runtime_obligation_5;
    foreign_ejson_runtime_totext =
    enhanced_foreign_ejson_runtime_obligation_6 }
