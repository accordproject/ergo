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

type dateTime = Calendar.t

(** Parse/Print *)
let from_string (x:string) : dateTime = Printer.Calendar.from_fstring "%d %b %Y %H:%M:%S" x
let to_string (x:dateTime) : string = Printer.Calendar.sprint "%d %b %Y %H:%M:%S" x

(** Initial *)
let now () : dateTime = Calendar.now()

(** Components *)
let day (x:dateTime) : int = Calendar.day_of_month x
let month (x:dateTime) : int = Date.int_of_month (Calendar.month x)
let quarter (x:dateTime) : int = ((month x) mod 3) + 1
let year (x:dateTime) : int = Calendar.year x

(** Comparisons *)
let eq (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 = 0
let ne (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 != 0
let lt (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 < 0
let le (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 <= 0
let gt (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 > 0
let ge (x1:dateTime) (x2:dateTime) : bool = Calendar.compare x1 x2 >= 0

(** Arithmetics *)

type duration = Calendar.Period.t

let deq (d1:duration) (d2:duration) : bool = Calendar.Period.equal d1 d2
let dfrom_string (x:string) : duration = raise Not_found
let dto_string (x:duration) : string = "_" (* XXX To be figured out *)
let dduration (x1:dateTime) (x2:dateTime) : duration = Calendar.sub x1 x2
let ddays (x1:dateTime) (x2:dateTime) : float =
  let d = Calendar.Period.to_date (dduration x1 x2) in
  let d = Date.Period.nb_days d in
  float_of_int d
let dseconds (x1:dateTime) (x2:dateTime) : float =
  let t = Calendar.Period.to_time (dduration x1 x2) in
  Time.Second.to_float (Time.Period.to_seconds t)

let plus (x1:dateTime) (d1:duration) : dateTime = Calendar.add x1 d1
let minus (x1:dateTime) (d1:duration) : dateTime = Calendar.rem x1 d1

