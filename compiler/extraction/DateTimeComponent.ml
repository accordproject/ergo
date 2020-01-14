open CoqLibAdd
open EquivDec
open ForeignData
open Java
open NativeString

type coq_DATE_TIME_FORMAT = Date_time_component.date_time_format

type coq_DATE_TIME_DURATION = Date_time_component.duration

type coq_DATE_TIME_PERIOD = Date_time_component.period

type coq_DATE_TIME = Date_time_component.dateTime

(** val date_time_format_foreign_data_obligation_3 :
    coq_DATE_TIME_FORMAT -> coq_DATE_TIME_FORMAT **)

let date_time_format_foreign_data_obligation_3 a =
  a

(** val date_time_format_foreign_data_obligation_1 :
    coq_DATE_TIME_FORMAT coq_EqDec **)

let date_time_format_foreign_data_obligation_1 x y =
  if (fun x y -> Date_time_component.format_eq x y) x y then true else false

(** val date_time_format_foreign_data_obligation_6 :
    coq_DATE_TIME_FORMAT coq_ToString **)

let date_time_format_foreign_data_obligation_6 =
  (fun x -> Util.char_list_of_string (Date_time_component.format_to_string x))

(** val date_time_format_foreign_data : foreign_data **)

let date_time_format_foreign_data =
  { foreign_data_dec =
    (Obj.magic date_time_format_foreign_data_obligation_1);
    foreign_data_normalize = (fun a ->
    Obj.magic date_time_format_foreign_data_obligation_3 a);
    foreign_data_tostring =
    (Obj.magic date_time_format_foreign_data_obligation_6) }

(** val date_time_duration_foreign_data_obligation_3 :
    coq_DATE_TIME_DURATION -> coq_DATE_TIME_DURATION **)

let date_time_duration_foreign_data_obligation_3 a =
  a

(** val date_time_duration_foreign_data_obligation_1 :
    coq_DATE_TIME_DURATION coq_EqDec **)

let date_time_duration_foreign_data_obligation_1 x y =
  if (fun x y -> Date_time_component.duration_eq x y) x y then true else false

(** val date_time_duration_foreign_data_obligation_6 :
    coq_DATE_TIME_DURATION coq_ToString **)

let date_time_duration_foreign_data_obligation_6 =
  (fun x -> Util.char_list_of_string (Date_time_component.duration_to_string x))

(** val date_time_duration_foreign_data : foreign_data **)

let date_time_duration_foreign_data =
  { foreign_data_dec =
    (Obj.magic date_time_duration_foreign_data_obligation_1);
    foreign_data_normalize = (fun a ->
    Obj.magic date_time_duration_foreign_data_obligation_3 a);
    foreign_data_tostring =
    (Obj.magic date_time_duration_foreign_data_obligation_6) }

(** val date_time_period_foreign_data_obligation_3 :
    coq_DATE_TIME_PERIOD -> coq_DATE_TIME_PERIOD **)

let date_time_period_foreign_data_obligation_3 a =
  a

(** val date_time_period_foreign_data_obligation_1 :
    coq_DATE_TIME_PERIOD coq_EqDec **)

let date_time_period_foreign_data_obligation_1 x y =
  if (fun x y -> Date_time_component.period_eq x y) x y then true else false

(** val date_time_period_foreign_data_obligation_6 :
    coq_DATE_TIME_PERIOD coq_ToString **)

let date_time_period_foreign_data_obligation_6 =
  (fun x -> Util.char_list_of_string (Date_time_component.period_to_string x))

(** val date_time_period_foreign_data : foreign_data **)

let date_time_period_foreign_data =
  { foreign_data_dec =
    (Obj.magic date_time_period_foreign_data_obligation_1);
    foreign_data_normalize = (fun a ->
    Obj.magic date_time_period_foreign_data_obligation_3 a);
    foreign_data_tostring =
    (Obj.magic date_time_period_foreign_data_obligation_6) }

(** val date_time_foreign_data_obligation_3 :
    coq_DATE_TIME -> coq_DATE_TIME **)

let date_time_foreign_data_obligation_3 a =
  a

(** val date_time_foreign_data_obligation_1 : coq_DATE_TIME coq_EqDec **)

let date_time_foreign_data_obligation_1 x y =
  if (fun x y -> Date_time_component.eq x y) x y then true else false

(** val date_time_foreign_data_obligation_6 : coq_DATE_TIME coq_ToString **)

let date_time_foreign_data_obligation_6 d =
  (fun x f -> Util.char_list_of_string (Date_time_component.to_string_format x f))
    d
    ((fun x -> Date_time_component.format_from_string (Util.string_of_char_list x))
      ('M'::('M'::('/'::('D'::('D'::('/'::('Y'::('Y'::('Y'::('Y'::[])))))))))))

(** val date_time_foreign_data : foreign_data **)

let date_time_foreign_data =
  { foreign_data_dec = (Obj.magic date_time_foreign_data_obligation_1);
    foreign_data_normalize = (fun a ->
    Obj.magic date_time_foreign_data_obligation_3 a); foreign_data_tostring =
    (Obj.magic date_time_foreign_data_obligation_6) }

type date_time_unary_op =
| Coq_uop_date_time_get_seconds
| Coq_uop_date_time_get_minutes
| Coq_uop_date_time_get_hours
| Coq_uop_date_time_get_days
| Coq_uop_date_time_get_weeks
| Coq_uop_date_time_get_months
| Coq_uop_date_time_get_quarters
| Coq_uop_date_time_get_years
| Coq_uop_date_time_start_of_day
| Coq_uop_date_time_start_of_week
| Coq_uop_date_time_start_of_month
| Coq_uop_date_time_start_of_quarter
| Coq_uop_date_time_start_of_year
| Coq_uop_date_time_end_of_day
| Coq_uop_date_time_end_of_week
| Coq_uop_date_time_end_of_month
| Coq_uop_date_time_end_of_quarter
| Coq_uop_date_time_end_of_year
| Coq_uop_date_time_format_from_string
| Coq_uop_date_time_from_string
| Coq_uop_date_time_max
| Coq_uop_date_time_min
| Coq_uop_date_time_duration_amount
| Coq_uop_date_time_duration_from_string
| Coq_uop_date_time_duration_from_seconds
| Coq_uop_date_time_duration_from_minutes
| Coq_uop_date_time_duration_from_hours
| Coq_uop_date_time_duration_from_days
| Coq_uop_date_time_duration_from_weeks
| Coq_uop_date_time_period_from_string
| Coq_uop_date_time_period_from_days
| Coq_uop_date_time_period_from_weeks
| Coq_uop_date_time_period_from_months
| Coq_uop_date_time_period_from_quarters
| Coq_uop_date_time_period_from_years

type date_time_binary_op =
| Coq_bop_date_time_format
| Coq_bop_date_time_add
| Coq_bop_date_time_subtract
| Coq_bop_date_time_add_period
| Coq_bop_date_time_subtract_period
| Coq_bop_date_time_is_same
| Coq_bop_date_time_is_before
| Coq_bop_date_time_is_after
| Coq_bop_date_time_diff

(** val date_time_unary_op_tostring : date_time_unary_op -> char list **)

let date_time_unary_op_tostring = function
| Coq_uop_date_time_get_seconds ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('S'::('e'::('c'::('o'::('n'::('d'::('s'::[])))))))))))))))))
| Coq_uop_date_time_get_minutes ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('M'::('i'::('n'::('u'::('t'::('e'::('s'::[])))))))))))))))))
| Coq_uop_date_time_get_hours ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('H'::('o'::('u'::('r'::('s'::[])))))))))))))))
| Coq_uop_date_time_get_days ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('D'::('a'::('y'::('s'::[]))))))))))))))
| Coq_uop_date_time_get_weeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('W'::('e'::('e'::('k'::('s'::[])))))))))))))))
| Coq_uop_date_time_get_months ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('M'::('o'::('n'::('t'::('h'::('s'::[]))))))))))))))))
| Coq_uop_date_time_get_quarters ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[]))))))))))))))))))
| Coq_uop_date_time_get_years ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('Y'::('e'::('a'::('r'::('s'::[])))))))))))))))
| Coq_uop_date_time_start_of_day ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('D'::('a'::('y'::[])))))))))))))))))
| Coq_uop_date_time_start_of_week ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('W'::('e'::('e'::('k'::[]))))))))))))))))))
| Coq_uop_date_time_start_of_month ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[])))))))))))))))))))
| Coq_uop_date_time_start_of_quarter ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))))
| Coq_uop_date_time_start_of_year ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('Y'::('e'::('a'::('r'::[]))))))))))))))))))
| Coq_uop_date_time_end_of_day ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('D'::('a'::('y'::[])))))))))))))))
| Coq_uop_date_time_end_of_week ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('W'::('e'::('e'::('k'::[]))))))))))))))))
| Coq_uop_date_time_end_of_month ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[])))))))))))))))))
| Coq_uop_date_time_end_of_quarter ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))
| Coq_uop_date_time_end_of_year ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('Y'::('e'::('a'::('r'::[]))))))))))))))))
| Coq_uop_date_time_format_from_string ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))
| Coq_uop_date_time_from_string ->
  'D'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))
| Coq_uop_date_time_max ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('a'::('x'::[]))))))))))
| Coq_uop_date_time_min ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('i'::('n'::[]))))))))))
| Coq_uop_date_time_duration_amount ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('A'::('m'::('o'::('u'::('n'::('t'::[])))))))))))))))))))))
| Coq_uop_date_time_duration_from_string ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))
| Coq_uop_date_time_duration_from_seconds ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('S'::('e'::('c'::('o'::('n'::('d'::('s'::[]))))))))))))))))))))))))))
| Coq_uop_date_time_duration_from_minutes ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('M'::('i'::('n'::('u'::('t'::('e'::('s'::[]))))))))))))))))))))))))))
| Coq_uop_date_time_duration_from_hours ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('H'::('o'::('u'::('r'::('s'::[]))))))))))))))))))))))))
| Coq_uop_date_time_duration_from_days ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('D'::('a'::('y'::('s'::[])))))))))))))))))))))))
| Coq_uop_date_time_duration_from_weeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('W'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))))
| Coq_uop_date_time_period_from_string ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))
| Coq_uop_date_time_period_from_days ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('D'::('a'::('y'::('s'::[])))))))))))))))))))))
| Coq_uop_date_time_period_from_weeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('W'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))
| Coq_uop_date_time_period_from_months ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('M'::('o'::('n'::('t'::('h'::('s'::[])))))))))))))))))))))))
| Coq_uop_date_time_period_from_quarters ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))
| Coq_uop_date_time_period_from_years ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('Y'::('e'::('a'::('r'::('s'::[]))))))))))))))))))))))

(** val date_time_binary_op_tostring : date_time_binary_op -> char list **)

let date_time_binary_op_tostring = function
| Coq_bop_date_time_format ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))
| Coq_bop_date_time_add ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('A'::('d'::('d'::[]))))))))))
| Coq_bop_date_time_subtract ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::[])))))))))))))))
| Coq_bop_date_time_add_period ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('A'::('d'::('d'::('P'::('e'::('r'::('i'::('o'::('d'::[]))))))))))))))))
| Coq_bop_date_time_subtract_period ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::('P'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))
| Coq_bop_date_time_is_same ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('S'::('a'::('m'::('e'::[])))))))))))))
| Coq_bop_date_time_is_before ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('B'::('e'::('f'::('o'::('r'::('e'::[])))))))))))))))
| Coq_bop_date_time_is_after ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('A'::('f'::('t'::('e'::('r'::[]))))))))))))))
| Coq_bop_date_time_diff ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('i'::('f'::('f'::[])))))))))))

(** val cname : nstring **)

let cname =
  nstring_quote
    ('D'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('C'::('o'::('m'::('p'::('o'::('n'::('e'::('n'::('t'::[])))))))))))))))))

(** val date_time_to_java_unary_op :
    int -> nstring -> nstring -> date_time_unary_op -> java_json -> java_json **)

let date_time_to_java_unary_op _ _ _ fu d =
  match fu with
  | Coq_uop_date_time_get_seconds ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('s'::('e'::('c'::('o'::('n'::('d'::('s'::[]))))))))))))))))))))))
      d
  | Coq_uop_date_time_get_minutes ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('m'::('i'::('n'::('u'::('t'::('e'::('s'::[]))))))))))))))))))))))
      d
  | Coq_uop_date_time_get_hours ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('h'::('o'::('u'::('r'::('s'::[]))))))))))))))))))))
      d
  | Coq_uop_date_time_get_days ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('d'::('a'::('y'::('s'::[])))))))))))))))))))
      d
  | Coq_uop_date_time_get_weeks ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('w'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))
      d
  | Coq_uop_date_time_get_months ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('m'::('o'::('n'::('t'::('h'::('s'::[])))))))))))))))))))))
      d
  | Coq_uop_date_time_get_quarters ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('y'::('e'::('a'::('r'::('s'::[]))))))))))))))))))))
      d
  | Coq_uop_date_time_get_years ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('g'::('e'::('t'::('_'::('q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))
      d
  | Coq_uop_date_time_start_of_day ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('t'::('a'::('r'::('t'::('_'::('o'::('f'::('_'::('d'::('a'::('y'::[])))))))))))))))))))))))
      d
  | Coq_uop_date_time_start_of_week ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('t'::('a'::('r'::('t'::('_'::('o'::('f'::('_'::('w'::('e'::('e'::('k'::[]))))))))))))))))))))))))
      d
  | Coq_uop_date_time_start_of_month ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('t'::('a'::('r'::('t'::('_'::('o'::('f'::('_'::('m'::('o'::('n'::('t'::('h'::[])))))))))))))))))))))))))
      d
  | Coq_uop_date_time_start_of_quarter ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('t'::('a'::('r'::('t'::('_'::('o'::('f'::('_'::('q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_start_of_year ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('t'::('a'::('r'::('t'::('_'::('o'::('f'::('_'::('y'::('e'::('a'::('r'::[]))))))))))))))))))))))))
      d
  | Coq_uop_date_time_end_of_day ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('e'::('n'::('d'::('_'::('o'::('f'::('_'::('d'::('a'::('y'::[])))))))))))))))))))))
      d
  | Coq_uop_date_time_end_of_week ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('e'::('n'::('d'::('_'::('o'::('f'::('_'::('w'::('e'::('e'::('k'::[]))))))))))))))))))))))
      d
  | Coq_uop_date_time_end_of_month ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('e'::('n'::('d'::('_'::('o'::('f'::('_'::('m'::('o'::('n'::('t'::('h'::[])))))))))))))))))))))))
      d
  | Coq_uop_date_time_end_of_quarter ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('e'::('n'::('d'::('_'::('o'::('f'::('_'::('q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))))))))
      d
  | Coq_uop_date_time_end_of_year ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('e'::('n'::('d'::('_'::('o'::('f'::('_'::('y'::('e'::('a'::('r'::[]))))))))))))))))))))))
      d
  | Coq_uop_date_time_format_from_string ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('f'::('o'::('r'::('m'::('a'::('t'::('_'::('f'::('r'::('o'::('m'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_from_string ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('f'::('r'::('o'::('m'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))))))))))))
      d
  | Coq_uop_date_time_max ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('m'::('a'::('x'::[]))))))))))))))
      d
  | Coq_uop_date_time_min ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('m'::('i'::('n'::[]))))))))))))))
      d
  | Coq_uop_date_time_duration_amount ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('a'::('m'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_string ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_seconds ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('s'::('e'::('c'::('o'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_minutes ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('m'::('i'::('n'::('u'::('t'::('e'::('s'::[]))))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_hours ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('h'::('o'::('u'::('r'::('s'::[]))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_days ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('d'::('a'::('y'::('s'::[])))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_duration_from_weeks ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('_'::('f'::('r'::('o'::('m'::('_'::('w'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_string ->
    mk_java_unary_op0
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_days ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('d'::('a'::('y'::('s'::[])))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_weeks ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('w'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_months ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('m'::('o'::('n'::('t'::('h'::('s'::[])))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_quarters ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))))))))
      d
  | Coq_uop_date_time_period_from_years ->
    mk_java_unary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::('_'::('f'::('r'::('o'::('m'::('_'::('y'::('e'::('a'::('r'::('s'::[]))))))))))))))))))))))))))))
      d

(** val date_time_to_java_binary_op :
    int -> nstring -> nstring -> date_time_binary_op -> java_json ->
    java_json -> java_json **)

let date_time_to_java_binary_op _ _ _ fb d1 d2 =
  match fb with
  | Coq_bop_date_time_format ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('f'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))))))
      d1 d2
  | Coq_bop_date_time_add ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('a'::('d'::('d'::[]))))))))))))))
      d1 d2
  | Coq_bop_date_time_subtract ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::[])))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_add_period ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('a'::('d'::('d'::('_'::('p'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_subtract_period ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('s'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::('_'::('p'::('e'::('r'::('i'::('d'::[])))))))))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_is_same ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('i'::('s'::('_'::('s'::('a'::('m'::('e'::[]))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_is_before ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('i'::('s'::('_'::('b'::('e'::('f'::('o'::('r'::('e'::[]))))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_is_after ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('i'::('s'::('_'::('a'::('f'::('t'::('e'::('r'::[])))))))))))))))))))
      d1 d2
  | Coq_bop_date_time_diff ->
    mk_java_binary_op0_foreign cname
      (nstring_quote
        ('d'::('a'::('t'::('e'::('_'::('t'::('i'::('m'::('e'::('_'::('d'::('i'::('f'::('f'::[])))))))))))))))
      d1 d2

type ejson_date_time_runtime_op =
| EJsonRuntimeDateTimeGetSeconds
| EJsonRuntimeDateTimeGetMinutes
| EJsonRuntimeDateTimeGetHours
| EJsonRuntimeDateTimeGetDays
| EJsonRuntimeDateTimeGetWeeks
| EJsonRuntimeDateTimeGetMonths
| EJsonRuntimeDateTimeGetQuarters
| EJsonRuntimeDateTimeGetYears
| EJsonRuntimeDateTimeStartOfDay
| EJsonRuntimeDateTimeStartOfWeek
| EJsonRuntimeDateTimeStartOfMonth
| EJsonRuntimeDateTimeStartOfQuarter
| EJsonRuntimeDateTimeStartOfYear
| EJsonRuntimeDateTimeEndOfDay
| EJsonRuntimeDateTimeEndOfWeek
| EJsonRuntimeDateTimeEndOfMonth
| EJsonRuntimeDateTimeEndOfQuarter
| EJsonRuntimeDateTimeEndOfYear
| EJsonRuntimeDateTimeFormatFromString
| EJsonRuntimeDateTimeFromString
| EJsonRuntimeDateTimeMax
| EJsonRuntimeDateTimeMin
| EJsonRuntimeDateTimeDurationAmount
| EJsonRuntimeDateTimeDurationFromString
| EJsonRuntimeDateTimePeriodFromString
| EJsonRuntimeDateTimeDurationFromSeconds
| EJsonRuntimeDateTimeDurationFromMinutes
| EJsonRuntimeDateTimeDurationFromHours
| EJsonRuntimeDateTimeDurationFromDays
| EJsonRuntimeDateTimeDurationFromWeeks
| EJsonRuntimeDateTimePeriodFromDays
| EJsonRuntimeDateTimePeriodFromWeeks
| EJsonRuntimeDateTimePeriodFromMonths
| EJsonRuntimeDateTimePeriodFromQuarters
| EJsonRuntimeDateTimePeriodFromYears
| EJsonRuntimeDateTimeFormat
| EJsonRuntimeDateTimeAdd
| EJsonRuntimeDateTimeSubtract
| EJsonRuntimeDateTimeAddPeriod
| EJsonRuntimeDateTimeSubtractPeriod
| EJsonRuntimeDateTimeIsSame
| EJsonRuntimeDateTimeIsBefore
| EJsonRuntimeDateTimeIsAfter
| EJsonRuntimeDateTimeDiff

(** val ejson_date_time_runtime_op_tostring :
    ejson_date_time_runtime_op -> char list **)

let ejson_date_time_runtime_op_tostring = function
| EJsonRuntimeDateTimeGetSeconds ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('S'::('e'::('c'::('o'::('n'::('d'::('s'::[])))))))))))))))))
| EJsonRuntimeDateTimeGetMinutes ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('M'::('i'::('n'::('u'::('t'::('e'::('s'::[])))))))))))))))))
| EJsonRuntimeDateTimeGetHours ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('H'::('o'::('u'::('r'::('s'::[])))))))))))))))
| EJsonRuntimeDateTimeGetDays ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('D'::('a'::('y'::('s'::[]))))))))))))))
| EJsonRuntimeDateTimeGetWeeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('W'::('e'::('e'::('k'::('s'::[])))))))))))))))
| EJsonRuntimeDateTimeGetMonths ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('M'::('o'::('n'::('t'::('h'::('s'::[]))))))))))))))))
| EJsonRuntimeDateTimeGetQuarters ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[]))))))))))))))))))
| EJsonRuntimeDateTimeGetYears ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('G'::('e'::('t'::('Y'::('e'::('a'::('r'::('s'::[])))))))))))))))
| EJsonRuntimeDateTimeStartOfDay ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('D'::('a'::('y'::[])))))))))))))))))
| EJsonRuntimeDateTimeStartOfWeek ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('W'::('e'::('e'::('k'::[]))))))))))))))))))
| EJsonRuntimeDateTimeStartOfMonth ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[])))))))))))))))))))
| EJsonRuntimeDateTimeStartOfQuarter ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))))
| EJsonRuntimeDateTimeStartOfYear ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('t'::('a'::('r'::('t'::('O'::('f'::('Y'::('e'::('a'::('r'::[]))))))))))))))))))
| EJsonRuntimeDateTimeEndOfDay ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('D'::('a'::('y'::[])))))))))))))))
| EJsonRuntimeDateTimeEndOfWeek ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('W'::('e'::('e'::('k'::[]))))))))))))))))
| EJsonRuntimeDateTimeEndOfMonth ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('M'::('o'::('n'::('t'::('h'::[])))))))))))))))))
| EJsonRuntimeDateTimeEndOfQuarter ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::[])))))))))))))))))))
| EJsonRuntimeDateTimeEndOfYear ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('E'::('n'::('d'::('O'::('f'::('Y'::('e'::('a'::('r'::[]))))))))))))))))
| EJsonRuntimeDateTimeFormatFromString ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))
| EJsonRuntimeDateTimeFromString ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))
| EJsonRuntimeDateTimeMax ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('a'::('x'::[]))))))))))
| EJsonRuntimeDateTimeMin ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('M'::('i'::('n'::[]))))))))))
| EJsonRuntimeDateTimeDurationAmount ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('A'::('m'::('o'::('u'::('n'::('t'::[])))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromString ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromString ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('S'::('t'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromSeconds ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('S'::('e'::('c'::('o'::('n'::('d'::('s'::[]))))))))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromMinutes ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('M'::('i'::('n'::('u'::('t'::('e'::('s'::[]))))))))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromHours ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('H'::('o'::('u'::('r'::('s'::[]))))))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromDays ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('D'::('a'::('y'::('s'::[])))))))))))))))))))))))
| EJsonRuntimeDateTimeDurationFromWeeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('u'::('r'::('a'::('t'::('i'::('o'::('n'::('F'::('r'::('o'::('m'::('W'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromDays ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('D'::('a'::('y'::('s'::[])))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromWeeks ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('W'::('e'::('e'::('k'::('s'::[]))))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromMonths ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('M'::('o'::('n'::('t'::('h'::('s'::[])))))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromQuarters ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('Q'::('u'::('a'::('r'::('t'::('e'::('r'::('s'::[])))))))))))))))))))))))))
| EJsonRuntimeDateTimePeriodFromYears ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('P'::('e'::('r'::('i'::('o'::('d'::('F'::('r'::('o'::('m'::('Y'::('e'::('a'::('r'::('s'::[]))))))))))))))))))))))
| EJsonRuntimeDateTimeFormat ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('F'::('o'::('r'::('m'::('a'::('t'::[])))))))))))))
| EJsonRuntimeDateTimeAdd ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('A'::('d'::('d'::[]))))))))))
| EJsonRuntimeDateTimeSubtract ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::[])))))))))))))))
| EJsonRuntimeDateTimeAddPeriod ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('A'::('d'::('d'::('P'::('e'::('r'::('i'::('o'::('d'::[]))))))))))))))))
| EJsonRuntimeDateTimeSubtractPeriod ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('S'::('u'::('b'::('t'::('r'::('a'::('c'::('t'::('P'::('e'::('r'::('i'::('o'::('d'::[])))))))))))))))))))))
| EJsonRuntimeDateTimeIsSame ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('S'::('a'::('m'::('e'::[])))))))))))))
| EJsonRuntimeDateTimeIsBefore ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('B'::('e'::('f'::('o'::('r'::('e'::[])))))))))))))))
| EJsonRuntimeDateTimeIsAfter ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('I'::('s'::('A'::('f'::('t'::('e'::('r'::[]))))))))))))))
| EJsonRuntimeDateTimeDiff ->
  'd'::('a'::('t'::('e'::('T'::('i'::('m'::('e'::('D'::('i'::('f'::('f'::[])))))))))))

(** val ejson_date_time_runtime_op_fromstring :
    char list -> ejson_date_time_runtime_op option **)

let ejson_date_time_runtime_op_fromstring = function
| [] -> None
| a::s0 ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then None
    else if b0
         then None
         else if b1
              then if b2
                   then None
                   else if b3
                        then None
                        else if b4
                             then if b5
                                  then if b6
                                       then None
                                       else (match s0 with
                                             | [] -> None
                                             | a0::s1 ->
                                               (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                 (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                 if b7
                                                 then if b8
                                                      then None
                                                      else if b9
                                                           then None
                                                           else if b10
                                                                then None
                                                                else 
                                                                  if b11
                                                                  then None
                                                                  else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then None
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    None
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then None
                                                                    else 
                                                                    if b16
                                                                    then None
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then None
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then None
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    None
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then None
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then None
                                                                    else 
                                                                    if b27
                                                                    then None
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then None
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    None
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then None
                                                                    else 
                                                                    if b32
                                                                    then None
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then None
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then None
                                                                    else 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then None
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    None
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    if b40
                                                                    then None
                                                                    else 
                                                                    if b41
                                                                    then None
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    if b43
                                                                    then None
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    if b46
                                                                    then None
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    None
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    if b48
                                                                    then None
                                                                    else 
                                                                    if b49
                                                                    then 
                                                                    if b50
                                                                    then 
                                                                    if b51
                                                                    then None
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    if b54
                                                                    then None
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    None
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then None
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then None
                                                                    else 
                                                                    if b59
                                                                    then None
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then None
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    None
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetWeeks
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetSeconds
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetMonths
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b97
                                                                    then None
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetMinutes
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetYears
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetQuarters
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then None
                                                                    else 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetDays
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeGetHours
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then None
                                                                    else 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeSubtract
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then None
                                                                    else 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then None
                                                                    else 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then None
                                                                    else 
                                                                    if b154
                                                                    then 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeSubtractPeriod
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then None
                                                                    else 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then None
                                                                    else 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeStartOfWeek
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then None
                                                                    else 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then None
                                                                    else 
                                                                    if b144
                                                                    then None
                                                                    else 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then None
                                                                    else 
                                                                    if b154
                                                                    then 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeStartOfMonth
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then None
                                                                    else 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then None
                                                                    else 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeStartOfYear
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then None
                                                                    else 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then None
                                                                    else 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeStartOfQuarter
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then None
                                                                    else 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeStartOfDay
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then None
                                                                    else 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeMin
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeMax
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then None
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeEndOfWeek
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeEndOfMonth
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeEndOfYear
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then None
                                                                    else 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then 
                                                                    if b153
                                                                    then None
                                                                    else 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeEndOfQuarter
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then None
                                                                    else 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeEndOfDay
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b66
                                                                    then 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then None
                                                                    else 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then None
                                                                    else 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then None
                                                                    else 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeIsSame
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then None
                                                                    else 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeIsAfter
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then None
                                                                    else 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeIsBefore
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then None
                                                                    else 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then None
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeAdd
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then None
                                                                    else 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then None
                                                                    else 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then None
                                                                    else 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeAddPeriod
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then None
                                                                    else 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeFormat
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then None
                                                                    else 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then None
                                                                    else 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeFormatFromString
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    if b73
                                                                    then None
                                                                    else 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then None
                                                                    else 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then None
                                                                    else 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then None
                                                                    else 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then 
                                                                    if b120
                                                                    then None
                                                                    else 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then None
                                                                    else 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeFromString
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then None
                                                                    else 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then None
                                                                    else 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then None
                                                                    else 
                                                                    if b96
                                                                    then None
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then None
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then None
                                                                    else 
                                                                    if b106
                                                                    then 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then 
                                                                    if b122
                                                                    then 
                                                                    if b123
                                                                    then None
                                                                    else 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then None
                                                                    else 
                                                                    if b129
                                                                    then None
                                                                    else 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then None
                                                                    else 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then None
                                                                    else 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationAmount
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then None
                                                                    else 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then None
                                                                    else 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then None
                                                                    else 
                                                                    if b136
                                                                    then 
                                                                    if b137
                                                                    then None
                                                                    else 
                                                                    if b138
                                                                    then None
                                                                    else 
                                                                    if b139
                                                                    then 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then 
                                                                    if b164
                                                                    then None
                                                                    else 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then None
                                                                    else 
                                                                    if b186
                                                                    then 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then 
                                                                    if b192
                                                                    then 
                                                                    if b193
                                                                    then None
                                                                    else 
                                                                    if b194
                                                                    then None
                                                                    else 
                                                                    if b195
                                                                    then 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromWeeks
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then 
                                                                    if b164
                                                                    then None
                                                                    else 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then 
                                                                    if b186
                                                                    then 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then None
                                                                    else 
                                                                    if b192
                                                                    then 
                                                                    if b193
                                                                    then 
                                                                    if b194
                                                                    then 
                                                                    if b195
                                                                    then None
                                                                    else 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    None
                                                                    | a24::s25 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b199 b200 b201 b202 b203 b204 b205 b206 ->
                                                                    if b199
                                                                    then None
                                                                    else 
                                                                    if b200
                                                                    then None
                                                                    else 
                                                                    if b201
                                                                    then 
                                                                    if b202
                                                                    then None
                                                                    else 
                                                                    if b203
                                                                    then None
                                                                    else 
                                                                    if b204
                                                                    then 
                                                                    if b205
                                                                    then 
                                                                    if b206
                                                                    then None
                                                                    else 
                                                                    (match s25 with
                                                                    | [] ->
                                                                    None
                                                                    | a25::s26 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b207 b208 b209 b210 b211 b212 b213 b214 ->
                                                                    if b207
                                                                    then 
                                                                    if b208
                                                                    then 
                                                                    if b209
                                                                    then None
                                                                    else 
                                                                    if b210
                                                                    then None
                                                                    else 
                                                                    if b211
                                                                    then 
                                                                    if b212
                                                                    then 
                                                                    if b213
                                                                    then 
                                                                    if b214
                                                                    then None
                                                                    else 
                                                                    (match s26 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromSeconds
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a25)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a24)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then None
                                                                    else 
                                                                    if b185
                                                                    then None
                                                                    else 
                                                                    if b186
                                                                    then 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then None
                                                                    else 
                                                                    if b192
                                                                    then 
                                                                    if b193
                                                                    then 
                                                                    if b194
                                                                    then 
                                                                    if b195
                                                                    then None
                                                                    else 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    None
                                                                    | a24::s25 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b199 b200 b201 b202 b203 b204 b205 b206 ->
                                                                    if b199
                                                                    then 
                                                                    if b200
                                                                    then 
                                                                    if b201
                                                                    then 
                                                                    if b202
                                                                    then None
                                                                    else 
                                                                    if b203
                                                                    then None
                                                                    else 
                                                                    if b204
                                                                    then 
                                                                    if b205
                                                                    then 
                                                                    if b206
                                                                    then None
                                                                    else 
                                                                    (match s25 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromString
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a24)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then None
                                                                    else 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then None
                                                                    else 
                                                                    if b185
                                                                    then 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then None
                                                                    else 
                                                                    if b192
                                                                    then None
                                                                    else 
                                                                    if b193
                                                                    then 
                                                                    if b194
                                                                    then None
                                                                    else 
                                                                    if b195
                                                                    then 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    None
                                                                    | a24::s25 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b199 b200 b201 b202 b203 b204 b205 b206 ->
                                                                    if b199
                                                                    then 
                                                                    if b200
                                                                    then None
                                                                    else 
                                                                    if b201
                                                                    then 
                                                                    if b202
                                                                    then None
                                                                    else 
                                                                    if b203
                                                                    then None
                                                                    else 
                                                                    if b204
                                                                    then 
                                                                    if b205
                                                                    then 
                                                                    if b206
                                                                    then None
                                                                    else 
                                                                    (match s25 with
                                                                    | [] ->
                                                                    None
                                                                    | a25::s26 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b207 b208 b209 b210 b211 b212 b213 b214 ->
                                                                    if b207
                                                                    then 
                                                                    if b208
                                                                    then 
                                                                    if b209
                                                                    then None
                                                                    else 
                                                                    if b210
                                                                    then None
                                                                    else 
                                                                    if b211
                                                                    then 
                                                                    if b212
                                                                    then 
                                                                    if b213
                                                                    then 
                                                                    if b214
                                                                    then None
                                                                    else 
                                                                    (match s26 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromMinutes
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a25)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a24)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then None
                                                                    else 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then None
                                                                    else 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromDays
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then None
                                                                    else 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then None
                                                                    else 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then None
                                                                    else 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then 
                                                                    if b192
                                                                    then 
                                                                    if b193
                                                                    then None
                                                                    else 
                                                                    if b194
                                                                    then None
                                                                    else 
                                                                    if b195
                                                                    then 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDurationFromHours
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b74
                                                                    then 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then None
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then None
                                                                    else 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    if b90
                                                                    then None
                                                                    else 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimeDiff
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else 
                                                                    if b66
                                                                    then None
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    if b68
                                                                    then None
                                                                    else 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then None
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    None
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then None
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then None
                                                                    else 
                                                                    if b75
                                                                    then None
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then None
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    None
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then None
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then None
                                                                    else 
                                                                    if b82
                                                                    then None
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then None
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    None
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then None
                                                                    else 
                                                                    if b89
                                                                    then None
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    if b91
                                                                    then None
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then None
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    None
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    if b98
                                                                    then 
                                                                    if b99
                                                                    then None
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then None
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    None
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then None
                                                                    else 
                                                                    if b104
                                                                    then None
                                                                    else 
                                                                    if b105
                                                                    then 
                                                                    if b106
                                                                    then None
                                                                    else 
                                                                    if b107
                                                                    then None
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    if b110
                                                                    then None
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    None
                                                                    | a13::s14 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b111 b112 b113 b114 b115 b116 b117 b118 ->
                                                                    if b111
                                                                    then None
                                                                    else 
                                                                    if b112
                                                                    then 
                                                                    if b113
                                                                    then 
                                                                    if b114
                                                                    then None
                                                                    else 
                                                                    if b115
                                                                    then None
                                                                    else 
                                                                    if b116
                                                                    then None
                                                                    else 
                                                                    if b117
                                                                    then 
                                                                    if b118
                                                                    then None
                                                                    else 
                                                                    (match s14 with
                                                                    | [] ->
                                                                    None
                                                                    | a14::s15 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b119 b120 b121 b122 b123 b124 b125 b126 ->
                                                                    if b119
                                                                    then None
                                                                    else 
                                                                    if b120
                                                                    then 
                                                                    if b121
                                                                    then None
                                                                    else 
                                                                    if b122
                                                                    then None
                                                                    else 
                                                                    if b123
                                                                    then 
                                                                    if b124
                                                                    then 
                                                                    if b125
                                                                    then 
                                                                    if b126
                                                                    then None
                                                                    else 
                                                                    (match s15 with
                                                                    | [] ->
                                                                    None
                                                                    | a15::s16 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b127 b128 b129 b130 b131 b132 b133 b134 ->
                                                                    if b127
                                                                    then 
                                                                    if b128
                                                                    then 
                                                                    if b129
                                                                    then 
                                                                    if b130
                                                                    then 
                                                                    if b131
                                                                    then None
                                                                    else 
                                                                    if b132
                                                                    then 
                                                                    if b133
                                                                    then 
                                                                    if b134
                                                                    then None
                                                                    else 
                                                                    (match s16 with
                                                                    | [] ->
                                                                    None
                                                                    | a16::s17 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b135 b136 b137 b138 b139 b140 b141 b142 ->
                                                                    if b135
                                                                    then 
                                                                    if b136
                                                                    then None
                                                                    else 
                                                                    if b137
                                                                    then 
                                                                    if b138
                                                                    then 
                                                                    if b139
                                                                    then None
                                                                    else 
                                                                    if b140
                                                                    then 
                                                                    if b141
                                                                    then 
                                                                    if b142
                                                                    then None
                                                                    else 
                                                                    (match s17 with
                                                                    | [] ->
                                                                    None
                                                                    | a17::s18 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b143 b144 b145 b146 b147 b148 b149 b150 ->
                                                                    if b143
                                                                    then 
                                                                    if b144
                                                                    then 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromWeeks
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then None
                                                                    else 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then None
                                                                    else 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then 
                                                                    if b171
                                                                    then None
                                                                    else 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromString
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then None
                                                                    else 
                                                                    if b160
                                                                    then 
                                                                    if b161
                                                                    then 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then None
                                                                    else 
                                                                    if b169
                                                                    then 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then 
                                                                    if b179
                                                                    then None
                                                                    else 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then 
                                                                    if b185
                                                                    then None
                                                                    else 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromMonths
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b146
                                                                    then 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then 
                                                                    if b176
                                                                    then 
                                                                    if b177
                                                                    then None
                                                                    else 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromYears
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b147
                                                                    then 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then None
                                                                    else 
                                                                    if b163
                                                                    then None
                                                                    else 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then None
                                                                    else 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    None
                                                                    | a21::s22 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b175 b176 b177 b178 b179 b180 b181 b182 ->
                                                                    if b175
                                                                    then None
                                                                    else 
                                                                    if b176
                                                                    then None
                                                                    else 
                                                                    if b177
                                                                    then 
                                                                    if b178
                                                                    then None
                                                                    else 
                                                                    if b179
                                                                    then 
                                                                    if b180
                                                                    then 
                                                                    if b181
                                                                    then 
                                                                    if b182
                                                                    then None
                                                                    else 
                                                                    (match s22 with
                                                                    | [] ->
                                                                    None
                                                                    | a22::s23 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b183 b184 b185 b186 b187 b188 b189 b190 ->
                                                                    if b183
                                                                    then 
                                                                    if b184
                                                                    then None
                                                                    else 
                                                                    if b185
                                                                    then 
                                                                    if b186
                                                                    then None
                                                                    else 
                                                                    if b187
                                                                    then None
                                                                    else 
                                                                    if b188
                                                                    then 
                                                                    if b189
                                                                    then 
                                                                    if b190
                                                                    then None
                                                                    else 
                                                                    (match s23 with
                                                                    | [] ->
                                                                    None
                                                                    | a23::s24 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b191 b192 b193 b194 b195 b196 b197 b198 ->
                                                                    if b191
                                                                    then None
                                                                    else 
                                                                    if b192
                                                                    then 
                                                                    if b193
                                                                    then None
                                                                    else 
                                                                    if b194
                                                                    then None
                                                                    else 
                                                                    if b195
                                                                    then 
                                                                    if b196
                                                                    then 
                                                                    if b197
                                                                    then 
                                                                    if b198
                                                                    then None
                                                                    else 
                                                                    (match s24 with
                                                                    | [] ->
                                                                    None
                                                                    | a24::s25 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b199 b200 b201 b202 b203 b204 b205 b206 ->
                                                                    if b199
                                                                    then 
                                                                    if b200
                                                                    then 
                                                                    if b201
                                                                    then None
                                                                    else 
                                                                    if b202
                                                                    then None
                                                                    else 
                                                                    if b203
                                                                    then 
                                                                    if b204
                                                                    then 
                                                                    if b205
                                                                    then 
                                                                    if b206
                                                                    then None
                                                                    else 
                                                                    (match s25 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromQuarters
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a24)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a23)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a22)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a21)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None
                                                                    else 
                                                                    if b144
                                                                    then None
                                                                    else 
                                                                    if b145
                                                                    then 
                                                                    if b146
                                                                    then None
                                                                    else 
                                                                    if b147
                                                                    then None
                                                                    else 
                                                                    if b148
                                                                    then None
                                                                    else 
                                                                    if b149
                                                                    then 
                                                                    if b150
                                                                    then None
                                                                    else 
                                                                    (match s18 with
                                                                    | [] ->
                                                                    None
                                                                    | a18::s19 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b151 b152 b153 b154 b155 b156 b157 b158 ->
                                                                    if b151
                                                                    then 
                                                                    if b152
                                                                    then None
                                                                    else 
                                                                    if b153
                                                                    then None
                                                                    else 
                                                                    if b154
                                                                    then None
                                                                    else 
                                                                    if b155
                                                                    then None
                                                                    else 
                                                                    if b156
                                                                    then 
                                                                    if b157
                                                                    then 
                                                                    if b158
                                                                    then None
                                                                    else 
                                                                    (match s19 with
                                                                    | [] ->
                                                                    None
                                                                    | a19::s20 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b159 b160 b161 b162 b163 b164 b165 b166 ->
                                                                    if b159
                                                                    then 
                                                                    if b160
                                                                    then None
                                                                    else 
                                                                    if b161
                                                                    then None
                                                                    else 
                                                                    if b162
                                                                    then 
                                                                    if b163
                                                                    then 
                                                                    if b164
                                                                    then 
                                                                    if b165
                                                                    then 
                                                                    if b166
                                                                    then None
                                                                    else 
                                                                    (match s20 with
                                                                    | [] ->
                                                                    None
                                                                    | a20::s21 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b167 b168 b169 b170 b171 b172 b173 b174 ->
                                                                    if b167
                                                                    then 
                                                                    if b168
                                                                    then 
                                                                    if b169
                                                                    then None
                                                                    else 
                                                                    if b170
                                                                    then None
                                                                    else 
                                                                    if b171
                                                                    then 
                                                                    if b172
                                                                    then 
                                                                    if b173
                                                                    then 
                                                                    if b174
                                                                    then None
                                                                    else 
                                                                    (match s21 with
                                                                    | [] ->
                                                                    Some
                                                                    EJsonRuntimeDateTimePeriodFromDays
                                                                    | _::_ ->
                                                                    None)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a20)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a19)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a18)
                                                                    else None
                                                                    else None)
                                                                    a17)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a16)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a15)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a14)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a13)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a12)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a11)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a10)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a9)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a8)
                                                                    else None
                                                                    else None)
                                                                    a7)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a6)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a5)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a4)
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a3)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a2)
                                                                    else None
                                                                    else None
                                                                    else None
                                                                    else None)
                                                                    a1)
                                                                    else None
                                                                    else None
                                                 else None)
                                                 a0)
                                  else None
                             else None
              else None)
    a
