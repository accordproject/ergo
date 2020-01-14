open BrandRelation
open CoqLibAdd
open Data
open DateTimeComponent
open EmitUtil
open EquivDec
open ForeignData
open ForeignOperators
open ForeignRuntime
open Lift
open LiftIterators
open List0
open LogComponent
open MathComponent
open MonetaryAmountComponent
open String0
open ToString
open UriComponent

let __ = let rec f _ = Obj.repr f in Obj.repr f

type enhanced_data =
| Coq_enhanceddateTimeformat of coq_DATE_TIME_FORMAT
| Coq_enhanceddateTime of coq_DATE_TIME
| Coq_enhanceddateTimeduration of coq_DATE_TIME_DURATION
| Coq_enhanceddateTimeperiod of coq_DATE_TIME_PERIOD

(** val enhanceddateTime_now : coq_DATE_TIME **)

let enhanceddateTime_now =
  (Date_time_component.now ())

(** val enhanced_foreign_data_obligation_3 :
    enhanced_data -> enhanced_data **)

let enhanced_foreign_data_obligation_3 a =
  a

(** val enhanced_foreign_data_obligation_1 : enhanced_data coq_EqDec **)

let enhanced_foreign_data_obligation_1 x y =
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

(** val enhanced_foreign_data_obligation_6 : enhanced_data coq_ToString **)

let enhanced_foreign_data_obligation_6 = function
| Coq_enhanceddateTimeformat d ->
  toString (Obj.magic date_time_format_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTime d ->
  toString (Obj.magic date_time_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTimeduration d ->
  toString (Obj.magic date_time_duration_foreign_data.foreign_data_tostring) d
| Coq_enhanceddateTimeperiod d ->
  toString (Obj.magic date_time_period_foreign_data.foreign_data_tostring) d

(** val enhanced_foreign_data : foreign_data **)

let enhanced_foreign_data =
  { foreign_data_dec = (Obj.magic enhanced_foreign_data_obligation_1);
    foreign_data_normalize = (fun a ->
    Obj.magic enhanced_foreign_data_obligation_3 a); foreign_data_tostring =
    (Obj.magic enhanced_foreign_data_obligation_6) }

(** val denhanceddateTimeformat : coq_DATE_TIME_FORMAT -> data **)

let denhanceddateTimeformat td =
  Coq_dforeign (Obj.magic (Coq_enhanceddateTimeformat td))

(** val denhanceddateTime : coq_DATE_TIME -> data **)

let denhanceddateTime td =
  Coq_dforeign (Obj.magic (Coq_enhanceddateTime td))

(** val denhanceddateTimeduration : coq_DATE_TIME_DURATION -> data **)

let denhanceddateTimeduration td =
  Coq_dforeign (Obj.magic (Coq_enhanceddateTimeduration td))

(** val denhanceddateTimeperiod : coq_DATE_TIME_PERIOD -> data **)

let denhanceddateTimeperiod td =
  Coq_dforeign (Obj.magic (Coq_enhanceddateTimeperiod td))

type enhanced_unary_op =
| Coq_enhanced_unary_uri_op of uri_unary_op
| Coq_enhanced_unary_log_op
| Coq_enhanced_unary_math_op of math_unary_op
| Coq_enhanced_unary_date_time_op of date_time_unary_op

(** val onddateTime : (coq_DATE_TIME -> 'a1) -> data -> 'a1 option **)

let onddateTime f = function
| Coq_dforeign f0 ->
  (match Obj.magic f0 with
   | Coq_enhanceddateTime fd -> Some (f fd)
   | _ -> None)
| _ -> None

(** val lift_dateTimeList : data list -> coq_DATE_TIME list option **)

let lift_dateTimeList l =
  lift_map (fun d ->
    match d with
    | Coq_dforeign f ->
      (match Obj.magic f with
       | Coq_enhanceddateTime fd -> Some fd
       | _ -> None)
    | _ -> None) l

(** val onddateTimeList :
    (coq_DATE_TIME list -> coq_DATE_TIME) -> data -> coq_DATE_TIME option **)

let onddateTimeList f d =
  let odates =
    match d with
    | Coq_dunit -> None
    | Coq_dnat _ -> None
    | Coq_dfloat _ -> None
    | Coq_dbool _ -> None
    | Coq_dstring _ -> None
    | Coq_dcoll c -> lift_dateTimeList c
    | _ -> None
  in
  lift f odates

(** val onddateTimeduration :
    (coq_DATE_TIME_DURATION -> 'a1) -> data -> 'a1 option **)

let onddateTimeduration f = function
| Coq_dforeign f0 ->
  (match Obj.magic f0 with
   | Coq_enhanceddateTimeduration fd -> Some (f fd)
   | _ -> None)
| _ -> None

(** val onddateTimeDurationNat : (int -> 'a1) -> data -> 'a1 option **)

let onddateTimeDurationNat f = function
| Coq_dnat z -> Some (f z)
| _ -> None

(** val onddateTimePeriodNat : (int -> 'a1) -> data -> 'a1 option **)

let onddateTimePeriodNat f = function
| Coq_dnat z -> Some (f z)
| _ -> None

(** val ondstring : (char list -> 'a1) -> data -> 'a1 option **)

let ondstring f = function
| Coq_dstring s -> Some (f s)
| _ -> None

(** val ondstringfloatopt :
    (char list -> float option) -> data -> data option **)

let ondstringfloatopt f = function
| Coq_dstring s ->
  (match f s with
   | Some n -> Some (dsome enhanced_foreign_data (Coq_dfloat n))
   | None -> Some (dnone enhanced_foreign_data))
| _ -> None

(** val ondstringunit : (char list -> unit) -> data -> data option **)

let ondstringunit f = function
| Coq_dstring s -> if unit_eqdec (f s) () then Some Coq_dunit else None
| _ -> None

(** val ondstringstring : (char list -> char list) -> data -> data option **)

let ondstringstring f = function
| Coq_dstring s -> Some (Coq_dstring (f s))
| _ -> None

(** val ondfloat : (float -> 'a1) -> data -> 'a1 option **)

let ondfloat f = function
| Coq_dfloat s -> Some (f s)
| _ -> None

(** val uri_unary_op_interp : uri_unary_op -> data -> data option **)

let uri_unary_op_interp op d =
  match op with
  | Coq_uop_uri_encode -> ondstringstring (fun x -> Uri_component.encode x) d
  | Coq_uop_uri_decode -> ondstringstring (fun x -> Uri_component.decode x) d

(** val log_unary_op_interp : data -> data option **)

let log_unary_op_interp d =
  ondstringunit (fun x -> Logger.log_string x) d

(** val math_unary_op_interp : math_unary_op -> data -> data option **)

let math_unary_op_interp op d =
  match op with
  | Coq_uop_math_float_of_string ->
    ondstringfloatopt (fun x -> Util.ergo_float_of_string x) d
  | Coq_uop_math_acos ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> acos x) d)
  | Coq_uop_math_asin ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> asin x) d)
  | Coq_uop_math_atan ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> atan x) d)
  | Coq_uop_math_cos ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> cos x) d)
  | Coq_uop_math_cosh ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> cosh x) d)
  | Coq_uop_math_sin ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> sin x) d)
  | Coq_uop_math_sinh ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> sinh x) d)
  | Coq_uop_math_tan ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> tan x) d)
  | Coq_uop_math_tanh ->
    lift (fun x -> Coq_dfloat x) (ondfloat (fun x -> tanh x) d)

(** val date_time_unary_op_interp :
    date_time_unary_op -> data -> data option **)

let date_time_unary_op_interp op d =
  match op with
  | Coq_uop_date_time_get_seconds ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_seconds x) d)
  | Coq_uop_date_time_get_minutes ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_minutes x) d)
  | Coq_uop_date_time_get_hours ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_hours x) d)
  | Coq_uop_date_time_get_days ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_days x) d)
  | Coq_uop_date_time_get_weeks ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_weeks x) d)
  | Coq_uop_date_time_get_months ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_months x) d)
  | Coq_uop_date_time_get_quarters ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_quarters x) d)
  | Coq_uop_date_time_get_years ->
    lift (fun x -> Coq_dnat x)
      (onddateTime (fun x -> Date_time_component.get_years x) d)
  | Coq_uop_date_time_start_of_day ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.start_of_day x) d)
  | Coq_uop_date_time_start_of_week ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.start_of_week x) d)
  | Coq_uop_date_time_start_of_month ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.start_of_month x) d)
  | Coq_uop_date_time_start_of_quarter ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.start_of_quarter x) d)
  | Coq_uop_date_time_start_of_year ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.start_of_year x) d)
  | Coq_uop_date_time_end_of_day ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.end_of_day x) d)
  | Coq_uop_date_time_end_of_week ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.end_of_week x) d)
  | Coq_uop_date_time_end_of_month ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.end_of_month x) d)
  | Coq_uop_date_time_end_of_quarter ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.end_of_quarter x) d)
  | Coq_uop_date_time_end_of_year ->
    lift denhanceddateTime
      (onddateTime (fun x -> Date_time_component.end_of_year x) d)
  | Coq_uop_date_time_format_from_string ->
    lift denhanceddateTimeformat
      (ondstring
        (fun x -> Date_time_component.format_from_string (Util.string_of_char_list x))
        d)
  | Coq_uop_date_time_from_string ->
    lift denhanceddateTime
      (ondstring
        (fun x -> Date_time_component.from_string (Util.string_of_char_list x))
        d)
  | Coq_uop_date_time_max ->
    lift denhanceddateTime
      (onddateTimeList (fun x -> Date_time_component.max x) d)
  | Coq_uop_date_time_min ->
    lift denhanceddateTime
      (onddateTimeList (fun x -> Date_time_component.min x) d)
  | Coq_uop_date_time_duration_amount ->
    lift (fun x -> Coq_dnat x)
      (onddateTimeduration (fun x -> Date_time_component.duration_amount x) d)
  | Coq_uop_date_time_duration_from_string ->
    lift denhanceddateTimeduration
      (ondstring
        (fun x -> Date_time_component.duration_from_string (Util.string_of_char_list x))
        d)
  | Coq_uop_date_time_duration_from_seconds ->
    lift denhanceddateTimeduration
      (onddateTimeDurationNat
        (fun x -> Date_time_component.duration_from_seconds x) d)
  | Coq_uop_date_time_duration_from_minutes ->
    lift denhanceddateTimeduration
      (onddateTimeDurationNat
        (fun x -> Date_time_component.duration_from_minutes x) d)
  | Coq_uop_date_time_duration_from_hours ->
    lift denhanceddateTimeduration
      (onddateTimeDurationNat
        (fun x -> Date_time_component.duration_from_hours x) d)
  | Coq_uop_date_time_duration_from_days ->
    lift denhanceddateTimeduration
      (onddateTimeDurationNat
        (fun x -> Date_time_component.duration_from_days x) d)
  | Coq_uop_date_time_duration_from_weeks ->
    lift denhanceddateTimeduration
      (onddateTimeDurationNat
        (fun x -> Date_time_component.duration_from_weeks x) d)
  | Coq_uop_date_time_period_from_string ->
    lift denhanceddateTimeperiod
      (ondstring
        (fun x -> Date_time_component.period_from_string (Util.string_of_char_list x))
        d)
  | Coq_uop_date_time_period_from_days ->
    lift denhanceddateTimeperiod
      (onddateTimePeriodNat (fun x -> Date_time_component.period_from_days x)
        d)
  | Coq_uop_date_time_period_from_weeks ->
    lift denhanceddateTimeperiod
      (onddateTimePeriodNat
        (fun x -> Date_time_component.period_from_weeks x) d)
  | Coq_uop_date_time_period_from_months ->
    lift denhanceddateTimeperiod
      (onddateTimePeriodNat
        (fun x -> Date_time_component.period_from_months x) d)
  | Coq_uop_date_time_period_from_quarters ->
    lift denhanceddateTimeperiod
      (onddateTimePeriodNat
        (fun x -> Date_time_component.period_from_quarters x) d)
  | Coq_uop_date_time_period_from_years ->
    lift denhanceddateTimeperiod
      (onddateTimePeriodNat
        (fun x -> Date_time_component.period_from_years x) d)

(** val enhanced_unary_op_interp :
    brand_relation_t -> enhanced_unary_op -> data -> data option **)

let enhanced_unary_op_interp _ op d =
  match op with
  | Coq_enhanced_unary_uri_op f -> uri_unary_op_interp f d
  | Coq_enhanced_unary_log_op -> log_unary_op_interp d
  | Coq_enhanced_unary_math_op f -> math_unary_op_interp f d
  | Coq_enhanced_unary_date_time_op f -> date_time_unary_op_interp f d

(** val enumToString : brands -> data -> char list **)

let rec enumToString b = function
| Coq_dleft d0 ->
  (match d0 with
   | Coq_dstring s ->
     append ('~'::[])
       (append (toString coq_ToString_brands b)
         (append ('.'::[]) (stringToString s)))
   | _ ->
     '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[]))))))))))))
| Coq_dright d0 -> enumToString b d0
| _ ->
  '<'::('B'::('O'::('G'::('U'::('S'::(' '::('E'::('N'::('U'::('M'::('>'::[])))))))))))

(** val dataToString : data -> char list **)

let rec dataToString = function
| Coq_dunit -> 'u'::('n'::('i'::('t'::[])))
| Coq_dnat n -> toString coq_ToString_Z n
| Coq_dfloat n -> toString coq_ToString_float n
| Coq_dbool b -> toString coq_ToString_bool b
| Coq_dstring s -> string_bracket ('"'::[]) (stringToString s) ('"'::[])
| Coq_dcoll l ->
  string_bracket ('['::[]) (concat (','::(' '::[])) (map dataToString l))
    (']'::[])
| Coq_drec lsd ->
  string_bracket ('{'::[])
    (concat (','::[])
      (map (fun xy ->
        let (x, y) = xy in
        append (stringToString x) (append (':'::[]) (dataToString y))) lsd))
    ('}'::[])
| Coq_dleft d0 ->
  string_bracket ('L'::('e'::('f'::('t'::('('::[]))))) (dataToString d0)
    (')'::[])
| Coq_dright d0 ->
  string_bracket ('R'::('i'::('g'::('h'::('t'::('('::[]))))))
    (dataToString d0) (')'::[])
| Coq_dbrand (b, d0) ->
  (match d0 with
   | Coq_drec _ ->
     append ('~'::[])
       (append (toString coq_ToString_brands b) (dataToString d0))
   | Coq_dleft _ -> enumToString b d0
   | Coq_dright _ -> enumToString b d0
   | _ ->
     '<'::('B'::('O'::('G'::('U'::('S'::(' '::('O'::('B'::('J'::('E'::('C'::('T'::('>'::[]))))))))))))))
| Coq_dforeign fd -> toString enhanced_foreign_data.foreign_data_tostring fd

(** val dataToText : data -> char list **)

let dataToText =
  dataToString

type enhanced_binary_op =
| Coq_enhanced_binary_math_op
| Coq_enhanced_binary_date_time_op of date_time_binary_op
| Coq_enhanced_binary_monetary_amount_op of monetary_amount_binary_op

(** val ondfloat2 : (float -> float -> 'a1) -> data -> data -> 'a1 option **)

let ondfloat2 f d1 d2 =
  match d1 with
  | Coq_dfloat fd1 ->
    (match d2 with
     | Coq_dfloat fd2 -> Some (f fd1 fd2)
     | _ -> None)
  | _ -> None

(** val onddateTime2 :
    (coq_DATE_TIME -> coq_DATE_TIME -> 'a1) -> data -> data -> 'a1 option **)

let onddateTime2 f d1 d2 =
  match d1 with
  | Coq_dforeign f0 ->
    (match Obj.magic f0 with
     | Coq_enhanceddateTime fd1 ->
       (match d2 with
        | Coq_dforeign f1 ->
          (match Obj.magic f1 with
           | Coq_enhanceddateTime fd2 -> Some (f fd1 fd2)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

(** val rondbooldateTime2 :
    (coq_DATE_TIME -> coq_DATE_TIME -> bool) -> data -> data -> data option **)

let rondbooldateTime2 f d1 d2 =
  lift (fun x -> Coq_dbool x) (onddateTime2 f d1 d2)

(** val math_binary_op_interp : data -> data -> data option **)

let math_binary_op_interp d1 d2 =
  lift (fun x -> Coq_dfloat x) (ondfloat2 (fun x y -> atan2 x y) d1 d2)

(** val date_time_binary_op_interp :
    date_time_binary_op -> data -> data -> data option **)

let date_time_binary_op_interp op d1 d2 =
  match op with
  | Coq_bop_date_time_format ->
    (match d1 with
     | Coq_dforeign f ->
       (match Obj.magic f with
        | Coq_enhanceddateTime tp ->
          (match d2 with
           | Coq_dforeign f0 ->
             (match Obj.magic f0 with
              | Coq_enhanceddateTimeformat td ->
                Some (Coq_dstring
                  ((fun x f -> Util.char_list_of_string (Date_time_component.to_string_format x f))
                    tp td))
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | Coq_bop_date_time_add ->
    (match d1 with
     | Coq_dforeign f ->
       (match Obj.magic f with
        | Coq_enhanceddateTime tp ->
          (match d2 with
           | Coq_dforeign f0 ->
             (match Obj.magic f0 with
              | Coq_enhanceddateTimeduration td ->
                Some
                  (denhanceddateTime
                    ((fun x y -> Date_time_component.add x y) tp td))
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | Coq_bop_date_time_subtract ->
    (match d1 with
     | Coq_dforeign f ->
       (match Obj.magic f with
        | Coq_enhanceddateTime tp ->
          (match d2 with
           | Coq_dforeign f0 ->
             (match Obj.magic f0 with
              | Coq_enhanceddateTimeduration td ->
                Some
                  (denhanceddateTime
                    ((fun x y ->  Date_time_component.subtract x y) tp td))
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | Coq_bop_date_time_add_period ->
    (match d1 with
     | Coq_dforeign f ->
       (match Obj.magic f with
        | Coq_enhanceddateTime tp ->
          (match d2 with
           | Coq_dforeign f0 ->
             (match Obj.magic f0 with
              | Coq_enhanceddateTimeperiod td ->
                Some
                  (denhanceddateTime
                    ((fun x y -> Date_time_component.add_period x y) tp td))
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | Coq_bop_date_time_subtract_period ->
    (match d1 with
     | Coq_dforeign f ->
       (match Obj.magic f with
        | Coq_enhanceddateTime tp ->
          (match d2 with
           | Coq_dforeign f0 ->
             (match Obj.magic f0 with
              | Coq_enhanceddateTimeperiod td ->
                Some
                  (denhanceddateTime
                    ((fun x y ->  Date_time_component.subtract_period x y) tp
                      td))
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | Coq_bop_date_time_is_same ->
    rondbooldateTime2 (fun x y -> Date_time_component.eq x y) d1 d2
  | Coq_bop_date_time_is_before ->
    rondbooldateTime2 (fun x y -> Date_time_component.is_before x y) d1 d2
  | Coq_bop_date_time_is_after ->
    rondbooldateTime2 (fun x y -> Date_time_component.is_after x y) d1 d2
  | Coq_bop_date_time_diff ->
    lift denhanceddateTimeduration
      (onddateTime2 (fun x y -> Date_time_component.diff x y) d1 d2)

(** val monetary_amount_binary_op_interp :
    monetary_amount_binary_op -> data -> data -> data option **)

let monetary_amount_binary_op_interp op d1 d2 =
  match op with
  | Coq_bop_monetary_amount_format ->
    (match d1 with
     | Coq_dfloat f1 ->
       (match d2 with
        | Coq_dstring s2 ->
          Some (Coq_dstring
            ((fun x1 f -> Util.char_list_of_string (MonetaryAmount.amount_to_string_format x1 (Util.string_of_char_list f)))
              f1 s2))
        | _ -> None)
     | _ -> None)
  | Coq_bop_monetary_code_format ->
    (match d1 with
     | Coq_dstring s1 ->
       (match d2 with
        | Coq_dstring s2 ->
          Some (Coq_dstring
            ((fun x1 f -> Util.char_list_of_string (MonetaryAmount.code_to_string_format (Util.string_of_char_list x1) (Util.string_of_char_list f)))
              s1 s2))
        | _ -> None)
     | _ -> None)

(** val enhanced_binary_op_interp :
    brand_relation_t -> enhanced_binary_op -> data -> data -> data option **)

let enhanced_binary_op_interp _ op d1 d2 =
  match op with
  | Coq_enhanced_binary_math_op -> math_binary_op_interp d1 d2
  | Coq_enhanced_binary_date_time_op f -> date_time_binary_op_interp f d1 d2
  | Coq_enhanced_binary_monetary_amount_op f ->
    monetary_amount_binary_op_interp f d1 d2

(** val enhanced_foreign_operators_obligation_1 :
    enhanced_unary_op coq_EqDec **)

let enhanced_foreign_operators_obligation_1 x y =
  match x with
  | Coq_enhanced_unary_uri_op x0 ->
    (match y with
     | Coq_enhanced_unary_uri_op u0 ->
       (match x0 with
        | Coq_uop_uri_encode ->
          (match u0 with
           | Coq_uop_uri_encode -> true
           | Coq_uop_uri_decode -> false)
        | Coq_uop_uri_decode ->
          (match u0 with
           | Coq_uop_uri_encode -> false
           | Coq_uop_uri_decode -> true))
     | _ -> false)
  | Coq_enhanced_unary_log_op ->
    (match y with
     | Coq_enhanced_unary_log_op -> true
     | _ -> false)
  | Coq_enhanced_unary_math_op x0 ->
    (match y with
     | Coq_enhanced_unary_math_op m0 ->
       (match x0 with
        | Coq_uop_math_float_of_string ->
          (match m0 with
           | Coq_uop_math_float_of_string -> true
           | _ -> false)
        | Coq_uop_math_acos ->
          (match m0 with
           | Coq_uop_math_acos -> true
           | _ -> false)
        | Coq_uop_math_asin ->
          (match m0 with
           | Coq_uop_math_asin -> true
           | _ -> false)
        | Coq_uop_math_atan ->
          (match m0 with
           | Coq_uop_math_atan -> true
           | _ -> false)
        | Coq_uop_math_cos ->
          (match m0 with
           | Coq_uop_math_cos -> true
           | _ -> false)
        | Coq_uop_math_cosh ->
          (match m0 with
           | Coq_uop_math_cosh -> true
           | _ -> false)
        | Coq_uop_math_sin ->
          (match m0 with
           | Coq_uop_math_sin -> true
           | _ -> false)
        | Coq_uop_math_sinh ->
          (match m0 with
           | Coq_uop_math_sinh -> true
           | _ -> false)
        | Coq_uop_math_tan ->
          (match m0 with
           | Coq_uop_math_tan -> true
           | _ -> false)
        | Coq_uop_math_tanh ->
          (match m0 with
           | Coq_uop_math_tanh -> true
           | _ -> false))
     | _ -> false)
  | Coq_enhanced_unary_date_time_op x0 ->
    (match y with
     | Coq_enhanced_unary_date_time_op d0 ->
       (match x0 with
        | Coq_uop_date_time_get_seconds ->
          (match d0 with
           | Coq_uop_date_time_get_seconds -> true
           | _ -> false)
        | Coq_uop_date_time_get_minutes ->
          (match d0 with
           | Coq_uop_date_time_get_minutes -> true
           | _ -> false)
        | Coq_uop_date_time_get_hours ->
          (match d0 with
           | Coq_uop_date_time_get_hours -> true
           | _ -> false)
        | Coq_uop_date_time_get_days ->
          (match d0 with
           | Coq_uop_date_time_get_days -> true
           | _ -> false)
        | Coq_uop_date_time_get_weeks ->
          (match d0 with
           | Coq_uop_date_time_get_weeks -> true
           | _ -> false)
        | Coq_uop_date_time_get_months ->
          (match d0 with
           | Coq_uop_date_time_get_months -> true
           | _ -> false)
        | Coq_uop_date_time_get_quarters ->
          (match d0 with
           | Coq_uop_date_time_get_quarters -> true
           | _ -> false)
        | Coq_uop_date_time_get_years ->
          (match d0 with
           | Coq_uop_date_time_get_years -> true
           | _ -> false)
        | Coq_uop_date_time_start_of_day ->
          (match d0 with
           | Coq_uop_date_time_start_of_day -> true
           | _ -> false)
        | Coq_uop_date_time_start_of_week ->
          (match d0 with
           | Coq_uop_date_time_start_of_week -> true
           | _ -> false)
        | Coq_uop_date_time_start_of_month ->
          (match d0 with
           | Coq_uop_date_time_start_of_month -> true
           | _ -> false)
        | Coq_uop_date_time_start_of_quarter ->
          (match d0 with
           | Coq_uop_date_time_start_of_quarter -> true
           | _ -> false)
        | Coq_uop_date_time_start_of_year ->
          (match d0 with
           | Coq_uop_date_time_start_of_year -> true
           | _ -> false)
        | Coq_uop_date_time_end_of_day ->
          (match d0 with
           | Coq_uop_date_time_end_of_day -> true
           | _ -> false)
        | Coq_uop_date_time_end_of_week ->
          (match d0 with
           | Coq_uop_date_time_end_of_week -> true
           | _ -> false)
        | Coq_uop_date_time_end_of_month ->
          (match d0 with
           | Coq_uop_date_time_end_of_month -> true
           | _ -> false)
        | Coq_uop_date_time_end_of_quarter ->
          (match d0 with
           | Coq_uop_date_time_end_of_quarter -> true
           | _ -> false)
        | Coq_uop_date_time_end_of_year ->
          (match d0 with
           | Coq_uop_date_time_end_of_year -> true
           | _ -> false)
        | Coq_uop_date_time_format_from_string ->
          (match d0 with
           | Coq_uop_date_time_format_from_string -> true
           | _ -> false)
        | Coq_uop_date_time_from_string ->
          (match d0 with
           | Coq_uop_date_time_from_string -> true
           | _ -> false)
        | Coq_uop_date_time_max ->
          (match d0 with
           | Coq_uop_date_time_max -> true
           | _ -> false)
        | Coq_uop_date_time_min ->
          (match d0 with
           | Coq_uop_date_time_min -> true
           | _ -> false)
        | Coq_uop_date_time_duration_amount ->
          (match d0 with
           | Coq_uop_date_time_duration_amount -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_string ->
          (match d0 with
           | Coq_uop_date_time_duration_from_string -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_seconds ->
          (match d0 with
           | Coq_uop_date_time_duration_from_seconds -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_minutes ->
          (match d0 with
           | Coq_uop_date_time_duration_from_minutes -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_hours ->
          (match d0 with
           | Coq_uop_date_time_duration_from_hours -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_days ->
          (match d0 with
           | Coq_uop_date_time_duration_from_days -> true
           | _ -> false)
        | Coq_uop_date_time_duration_from_weeks ->
          (match d0 with
           | Coq_uop_date_time_duration_from_weeks -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_string ->
          (match d0 with
           | Coq_uop_date_time_period_from_string -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_days ->
          (match d0 with
           | Coq_uop_date_time_period_from_days -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_weeks ->
          (match d0 with
           | Coq_uop_date_time_period_from_weeks -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_months ->
          (match d0 with
           | Coq_uop_date_time_period_from_months -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_quarters ->
          (match d0 with
           | Coq_uop_date_time_period_from_quarters -> true
           | _ -> false)
        | Coq_uop_date_time_period_from_years ->
          (match d0 with
           | Coq_uop_date_time_period_from_years -> true
           | _ -> false))
     | _ -> false)

(** val enhanced_foreign_operators_obligation_2 :
    enhanced_unary_op coq_ToString **)

let enhanced_foreign_operators_obligation_2 = function
| Coq_enhanced_unary_uri_op u -> uri_unary_op_tostring u
| Coq_enhanced_unary_log_op -> log_unary_op_tostring __
| Coq_enhanced_unary_math_op m -> math_unary_op_tostring m
| Coq_enhanced_unary_date_time_op d -> date_time_unary_op_tostring d

(** val enhanced_foreign_operators_obligation_4 :
    enhanced_binary_op coq_EqDec **)

let enhanced_foreign_operators_obligation_4 x y =
  match x with
  | Coq_enhanced_binary_math_op ->
    (match y with
     | Coq_enhanced_binary_math_op -> true
     | _ -> false)
  | Coq_enhanced_binary_date_time_op x0 ->
    (match y with
     | Coq_enhanced_binary_date_time_op d0 ->
       (match x0 with
        | Coq_bop_date_time_format ->
          (match d0 with
           | Coq_bop_date_time_format -> true
           | _ -> false)
        | Coq_bop_date_time_add ->
          (match d0 with
           | Coq_bop_date_time_add -> true
           | _ -> false)
        | Coq_bop_date_time_subtract ->
          (match d0 with
           | Coq_bop_date_time_subtract -> true
           | _ -> false)
        | Coq_bop_date_time_add_period ->
          (match d0 with
           | Coq_bop_date_time_add_period -> true
           | _ -> false)
        | Coq_bop_date_time_subtract_period ->
          (match d0 with
           | Coq_bop_date_time_subtract_period -> true
           | _ -> false)
        | Coq_bop_date_time_is_same ->
          (match d0 with
           | Coq_bop_date_time_is_same -> true
           | _ -> false)
        | Coq_bop_date_time_is_before ->
          (match d0 with
           | Coq_bop_date_time_is_before -> true
           | _ -> false)
        | Coq_bop_date_time_is_after ->
          (match d0 with
           | Coq_bop_date_time_is_after -> true
           | _ -> false)
        | Coq_bop_date_time_diff ->
          (match d0 with
           | Coq_bop_date_time_diff -> true
           | _ -> false))
     | _ -> false)
  | Coq_enhanced_binary_monetary_amount_op x0 ->
    (match y with
     | Coq_enhanced_binary_monetary_amount_op m0 ->
       (match x0 with
        | Coq_bop_monetary_amount_format ->
          (match m0 with
           | Coq_bop_monetary_amount_format -> true
           | Coq_bop_monetary_code_format -> false)
        | Coq_bop_monetary_code_format ->
          (match m0 with
           | Coq_bop_monetary_amount_format -> false
           | Coq_bop_monetary_code_format -> true))
     | _ -> false)

(** val enhanced_foreign_operators_obligation_5 :
    enhanced_binary_op coq_ToString **)

let enhanced_foreign_operators_obligation_5 = function
| Coq_enhanced_binary_math_op -> math_binary_op_tostring __
| Coq_enhanced_binary_date_time_op d -> date_time_binary_op_tostring d
| Coq_enhanced_binary_monetary_amount_op m ->
  monetary_amount_binary_op_tostring m

(** val enhanced_foreign_operators : foreign_operators **)

let enhanced_foreign_operators =
  { foreign_operators_unary_dec =
    (Obj.magic enhanced_foreign_operators_obligation_1);
    foreign_operators_unary_tostring =
    (Obj.magic enhanced_foreign_operators_obligation_2);
    foreign_operators_unary_interp = (Obj.magic enhanced_unary_op_interp);
    foreign_operators_binary_dec =
    (Obj.magic enhanced_foreign_operators_obligation_4);
    foreign_operators_binary_tostring =
    (Obj.magic enhanced_foreign_operators_obligation_5);
    foreign_operators_binary_interp = (Obj.magic enhanced_binary_op_interp);
    foreign_operators_unary_data_tostring = dataToString;
    foreign_operators_unary_data_totext = dataToText }

(** val enhanced_foreign_runtime : foreign_runtime **)

let enhanced_foreign_runtime =
  { foreign_runtime_data = enhanced_foreign_data; foreign_runtime_operators =
    enhanced_foreign_operators }
