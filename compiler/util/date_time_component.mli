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

(** Formats *)
(** Those are taken from the Accord Project specification:
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

type date_time_format
val format_eq : date_time_format -> date_time_format -> bool
val format_from_string : string -> date_time_format

(** Duration *)
type duration
val duration_eq : duration -> duration -> bool
val duration_to_string : duration -> string
val duration_from_string : string -> duration
val duration_amount : duration -> int

val duration_from_seconds : int -> duration
val duration_from_minutes : int -> duration
val duration_from_hours : int -> duration
val duration_from_days : int -> duration
val duration_from_weeks : int -> duration

val duration_seconds : int -> duration
val duration_minutes : int -> duration
val duration_hours : int -> duration
val duration_days : int -> duration
val duration_weeks : int -> duration

(** Period *)
type period
val period_eq : period -> period -> bool
val period_to_string : period -> string
val period_from_string : string -> period

val period_from_days : int -> period
val period_from_weeks : int -> period
val period_from_months : int -> period
val period_from_quarters : int -> period
val period_from_years : int -> period

val period_days : int -> period
val period_weeks : int -> period
val period_months : int -> period
val period_quarters : int -> period
val period_years : int -> period

(** DateTime *)
type dateTime
val eq : dateTime -> dateTime -> bool

(** Initial *)
val now : unit -> dateTime

(** Serialize/deserialize *)
val from_string : string -> dateTime
val format_to_string : date_time_format -> string
val to_string_format : dateTime -> date_time_format -> string

(** Components *)
val get_seconds : dateTime -> int
val get_minutes : dateTime -> int
val get_hours : dateTime -> int
val get_days : dateTime -> int
val get_weeks : dateTime -> int
val get_months : dateTime -> int
val get_quarters : dateTime -> int
val get_years : dateTime -> int

(** Min/Max *)
val max : dateTime list -> dateTime
val min : dateTime list -> dateTime

(** Comparisons *)
val is_before : dateTime -> dateTime -> bool
val is_after : dateTime -> dateTime -> bool

(** Start/End of period *)
val start_of_day : dateTime -> dateTime
val start_of_week : dateTime -> dateTime
val start_of_month : dateTime -> dateTime
val start_of_quarter : dateTime -> dateTime
val start_of_year : dateTime -> dateTime

val end_of_day : dateTime -> dateTime
val end_of_week : dateTime -> dateTime
val end_of_month : dateTime -> dateTime
val end_of_quarter : dateTime -> dateTime
val end_of_year : dateTime -> dateTime

(** Arithmetics *)
val diff : dateTime -> dateTime -> duration
val diff_days : dateTime -> dateTime -> float
val diff_seconds : dateTime -> dateTime -> float

val add : dateTime -> duration -> dateTime
val subtract : dateTime -> duration -> dateTime

val add_period : dateTime -> period -> dateTime
val subtract_period : dateTime -> period -> dateTime

