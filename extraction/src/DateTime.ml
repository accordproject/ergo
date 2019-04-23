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

(** Native OCaml support for the Ergo DateTime library *)

open CalendarLib

(** Misc *)
let undefined_error op =
  raise (Failure ("Operation " ^ op ^ " not defined in REPL"))

(** Parse/Print *)
let lift_error fcont f x =
  begin try f x with
  | _ -> fcont x
  end
let rec lift_error_map fl fe =
  begin match fl with
  | [] -> fe
  | f::morefl ->
      lift_error (lift_error_map morefl fe) f
  end
type format =
  | FDate of string
  | FDateTime of string
let f_of_format fmt =
  begin match fmt with
  | FDateTime s ->
      (fun x ->
         Printer.Calendar.from_fstring s x)
  | FDate s ->
      (fun x ->
         let d = Printer.Date.from_fstring s x in
         Calendar.create d (Time.lmake ()))
  end
let multi_parse fl fe x =
  lift_error_map (List.map f_of_format fl) fe x

let iso8610 =
  [ FDate "%Y-%m-%d";
    FDate "%Y%m%d";
    FDateTime "%Y-%m-%dT%H:%M:%S";
    FDateTime "%Y-%m-%d %H:%M:%S";
    FDateTime "%Y-%m-%dT%H:%M:%S%:z";
    FDateTime "%Y-%m-%d %H:%M:%S%:z";
    FDate "%d %b %Y";
    FDate "%d %b %y";
    FDateTime "%d %b %y %H:%M:%S";
    FDateTime "%d %b %Y %H:%M:%S";
    FDateTime "%d %b %y %H:%M:%S %z";
    FDateTime "%d %b %Y %H:%M:%S %z";
    FDate "%a %d %b %Y";
    FDate "%a %d %b %y";
    FDateTime "%a %d %b %y %H:%M:%S";
    FDateTime "%a %d %b %Y %H:%M:%S";
    FDateTime "%a %d %b %y %H:%M:%S %z";
    FDateTime "%a %d %b %Y %H:%M:%S %z";
    FDate "%a, %d %b %Y";
    FDate "%a, %d %b %y";
    FDateTime "%a, %d %b %y %H:%M:%S";
    FDateTime "%a, %d %b %Y %H:%M:%S";
    FDateTime "%a, %d %b %y %H:%M:%S %z";
    FDateTime "%a, %d %b %Y %H:%M:%S %z"; ]

(** Duration *)
type duration = Calendar.Period.t
let duration_eq (d1:duration) (d2:duration) : bool = Calendar.Period.equal d1 d2
let duration_amount (x:duration) : int = Calendar.Time.Period.to_seconds (Calendar.Period.to_time x)
let duration_to_string (x:duration) : string = "_" (* XXX To be figured out *)
let duration_from_string (x:string) : duration = undefined_error "duration_from_string"

(** Period *)
type period = Calendar.Period.t

let period_eq (d1:period) (d2:period) : bool = Calendar.Period.equal d1 d2
let period_to_string (x:duration) : string = "_" (* XXX To be figured out *)
let period_from_string (x:string) : period = undefined_error "period_from_string"

(** DateTime *)
type dateTime = Calendar.t

(** Initial *)
let now () : dateTime = Calendar.now()

(** Serialize/deserialize *)
let lower_bound, upper_bound =
  let compute () =
    let midnight = Calendar.Time.midnight () in
    let low, up =
	    Calendar.create (Calendar.Date.make 1 1 1) midnight,
      Calendar.create (Calendar.Date.make 3268 1 21) midnight
    in
    low, up
  in
  Time_Zone.on compute Time_Zone.UTC ()
let maximum_dateTime : dateTime = upper_bound
let minimum_dateTime : dateTime = lower_bound
let error_dt (x:string) : dateTime = minimum_dateTime
let from_string (x:string) : dateTime =
  multi_parse iso8610 error_dt x

(** Components *)
let get_second (x:dateTime) : int = Calendar.Time.second (Calendar.to_time x)
let get_minute (x:dateTime) : int = Calendar.Time.minute (Calendar.to_time x)
let get_hour (x:dateTime) : int = Calendar.Time.hour (Calendar.to_time x)
let get_day (x:dateTime) : int = Calendar.day_of_month x
let get_week (x:dateTime) : int = Calendar.week x
let get_month (x:dateTime) : int = Date.int_of_month (Calendar.month x)
let get_quarter (x:dateTime) : int = ((get_month x) / 3) + 1
let get_year (x:dateTime) : int = Calendar.year x

(** Comparisons *)
let eq (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 = 0
let is_before (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 < 0
let is_after (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 > 0

(** Min/Max *)
let max (xl:dateTime list) : dateTime =
  List.fold_left (fun a x -> if is_after a x then a else x) minimum_dateTime xl
let min (xl:dateTime list) : dateTime =
  List.fold_left (fun a x -> if is_before a x then a else x) maximum_dateTime xl

(** Arithmetics *)
let diff (x1:dateTime) (x2:dateTime) : duration = Calendar.sub x1 x2
let diff_days (x1:dateTime) (x2:dateTime) : float =
  let d = Calendar.Period.to_date (diff x1 x2) in
  let d = Date.Period.nb_days d in
  float_of_int d
let diff_seconds (x1:dateTime) (x2:dateTime) : float =
  let t = Calendar.Period.to_time (diff x1 x2) in
  Time.Second.to_float (Time.Period.to_seconds t)

let add (x1:dateTime) (d1:duration) : dateTime = Calendar.add x1 d1
let subtract (x1:dateTime) (d1:duration) : dateTime = Calendar.rem x1 d1

let add_period (x1:dateTime) (d1:period) : dateTime = Calendar.add x1 d1
let subtract_period (x1:dateTime) (d1:period) : dateTime = Calendar.rem x1 d1

let start_of_day (x1:dateTime) = undefined_error "start_of_day"
let start_of_week (x1:dateTime) = undefined_error "start_of_week"
let start_of_month (x1:dateTime) = undefined_error "start_of_month"
let start_of_quarter (x1:dateTime) = undefined_error "start_of_quarter"
let start_of_year (x1:dateTime) = undefined_error "start_of_year"

let end_of_day (x1:dateTime) = undefined_error "end_of_day"
let end_of_week (x1:dateTime) = undefined_error "end_of_week"
let end_of_month (x1:dateTime) = undefined_error "end_of_month"
let end_of_quarter (x1:dateTime) = undefined_error "end_of_quarter"
let end_of_year (x1:dateTime) = undefined_error "end_of_year"

let duration_seconds (x:int) = Calendar.Period.second x
let duration_minutes (x:int) = Calendar.Period.minute x
let duration_hours (x:int) = Calendar.Period.hour x
let duration_days (x:int) = Calendar.Period.day x
let duration_weeks (x:int) = Calendar.Period.week x

let period_days (x:int) = Calendar.Period.day x
let period_weeks (x:int) = Calendar.Period.week x
let period_months (x:int) = Calendar.Period.month x
let period_quarters (x:int) = Calendar.Period.month (x * 3)
let period_years (x:int) = Calendar.Period.year x

(* Formats *)

type date_time_format = string

(* From AP spec:
YYYY         2014               4 or 2 digit year
YY           14                 2 digit year
MMMM         December           Long month name
MMM          Feb.               Short month name
MM           04                 2 digit month number
M            12                 1 or 2 digit month number
DD           04                 2 digit day of month
D            3                  1 or 2 digit day of month
HH           04                 2 digit hours
H            3                  1 or 2 digit hours
mm           59                 2 digit minutes
ss           34                 2 digit seconds
SSS          002                3 digit milliseconds
Z            +01:00             UTC offset
*)

let conversion_table = [
  ("YYYY", "%Y");
  ("YY", "%y");
  ("MMMM", "%B");
  ("MMM", "%b.");
  ("MM", "%m");
  ("M", "%-m");
  ("DD", "%d");
  ("D", "%-d");
  ("HH", "%H");
  ("H", "%-H");
  ("mm", "%M");
  ("ss", "%S");
  ("SSS", ".000");
  ("Z", "%:z");
]
let apply_one_conv fout (f1,f2) =
  fout := Re.Str.global_replace (Re.Str.regexp_string f1) f2 !fout

let format_conversion f =
  let fout = ref f in
  List.iter (apply_one_conv fout) conversion_table;
  !fout

let format_eq (x:date_time_format) (y:date_time_format) : bool = x = y
let format_to_string (x:date_time_format) : string = x
let format_from_string (x:string) : date_time_format = x

let to_string_format (x:dateTime) (f:date_time_format) : string =
  Printer.Calendar.sprint (format_conversion f) x
