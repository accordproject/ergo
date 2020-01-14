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

Require Import List.
Require Import ZArith.
Require Import EquivDec.
Require Import RelationClasses.
Require Import Equivalence.
Require Import String.

Require Import Qcert.Utils.Utils.
Require Import Qcert.Brands.BrandRelation.
Require Import Qcert.EJson.EJsonSystem.
Require Import Qcert.Data.DataSystem.

Require Import Qcert.Compiler.Component.UriComponent.
Require Import LogComponent.
Require Import MathComponent.
Require Import DateTimeComponent.

Require Import QcertData.

Import ListNotations.
Local Open Scope string.
Local Open Scope list_scope.

Definition enhanced_ejson : Set := enhanced_data.

Program Instance enhanced_foreign_ejson : foreign_ejson
  := mk_foreign_ejson enhanced_ejson _ _ _ _ _ _.
Next Obligation.
  red.
  unfold equiv, complement.
  destruct x; destruct y; simpl; try solve [right; inversion 1].
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_format_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_duration_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
  - destruct (@equiv_dec _ _ _ (@foreign_data_dec date_time_period_foreign_data) d d0).
    + left; congruence.
    + right; congruence.
Defined.
Next Obligation.
  (* normalized? *)
  destruct a.
  - exact True.
  - exact (@foreign_data_normalized date_time_foreign_data d).
  - exact (@foreign_data_normalized date_time_duration_foreign_data d).
  - exact (@foreign_data_normalized date_time_period_foreign_data d).
Defined.
Next Obligation.
  destruct a.
  - simpl; trivial.
  - exact (@foreign_data_normalize_normalizes date_time_foreign_data d).
  - exact (@foreign_data_normalize_normalizes date_time_duration_foreign_data d).
  - exact (@foreign_data_normalize_normalizes date_time_period_foreign_data d).
Defined.
Next Obligation.
  constructor.
  destruct 1.
  - exact (@toString _ (@foreign_data_tostring date_time_format_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_duration_foreign_data) d).
  - exact (@toString _ (@foreign_data_tostring date_time_period_foreign_data) d).
Defined.

Inductive enhanced_foreign_ejson_runtime_op :=
| enhanced_ejson_uri : ejson_uri_runtime_op -> enhanced_foreign_ejson_runtime_op
| enhanced_ejson_log : ejson_log_runtime_op -> enhanced_foreign_ejson_runtime_op
| enhanced_ejson_math : ejson_math_runtime_op -> enhanced_foreign_ejson_runtime_op
| enhanced_ejson_date_time : ejson_date_time_runtime_op -> enhanced_foreign_ejson_runtime_op
.

Definition enhanced_foreign_ejson_runtime_op_tostring op : string :=
  match op with
  | enhanced_ejson_uri sop => ejson_uri_runtime_op_tostring sop
  | enhanced_ejson_log sop => ejson_log_runtime_op_tostring sop
  | enhanced_ejson_math sop => ejson_math_runtime_op_tostring sop
  | enhanced_ejson_date_time sop => ejson_date_time_runtime_op_tostring sop
  end.

Definition enhanced_ejson_uri_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  | EJsonRuntimeUriEncode =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejstring (URI_encode s))
         | _ => None
         end) dl
  | EJsonRuntimeUriDecode =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejstring (URI_decode s))
         | _ => None
         end) dl
  end.

Definition onjstringunit (f : String.string -> unit) (j : ejson) : option ejson :=
  match j with
  | ejstring s =>
    match f s with                                            (* Call log *)
    | y => if unit_eqdec y tt then Some ejnull else None      (* Return unit *)
    end
  | _ => None
  end.

Definition enhanced_ejson_log_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  | EJsonRuntimeLogString =>
    apply_unary
      (onjstringunit LOG_string) dl
  end.

Definition enhanced_ejson_math_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  | EJsonRuntimeFloatOfString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s =>
           match FLOAT_of_string s with
           | None => Some (ejobject (("$right",ejnull)::nil))
           | Some f => Some (ejobject (("$left",ejnumber f)::nil))
           end
         | _ => None
         end) dl
  | EJsonRuntimeAcos =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_acos f))
         | _ => None
         end) dl
  | EJsonRuntimeAsin =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_asin f))
         | _ => None
         end) dl
  | EJsonRuntimeAtan =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_atan f))
         | _ => None
         end) dl
  | EJsonRuntimeAtan2 =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejnumber f1, ejnumber f2 => Some (ejnumber (FLOAT_atan2 f1 f2))
         | _, _ => None
         end) dl
  | EJsonRuntimeCos =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_cos f))
         | _ => None
         end) dl
  | EJsonRuntimeCosh =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_cosh f))
         | _ => None
         end) dl
  | EJsonRuntimeSin =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_sin f))
         | _ => None
         end) dl
  | EJsonRuntimeSinh =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_sinh f))
         | _ => None
         end) dl
  | EJsonRuntimeTan =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_tan f))
         | _ => None
         end) dl
  | EJsonRuntimeTanh =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejnumber f => Some (ejnumber (FLOAT_tanh f))
         | _ => None
         end) dl
  end.

Fixpoint ejson_dates (d:list ejson) : option (list DATE_TIME) :=
  match d with
  | nil => Some nil
  | (ejforeign (enhanceddateTime d)) :: d' =>
    match ejson_dates d' with
    | Some s' => Some (d::s')
    | None => None
    end
  | _ => None
  end.

Definition enhanced_ejson_date_time_runtime_op_interp op (dl:list ejson) : option ejson :=
  match op with
  (* Unary *)
  | EJsonRuntimeDateTimeGetSeconds =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_seconds d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetMinutes =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_minutes d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetHours =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_hours d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetDays =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_days d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetWeeks =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_weeks d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetMonths =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_months d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetQuarters =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_quarters d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeGetYears =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejbigint (DATE_TIME_get_years d))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeStartOfDay =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_start_of_day d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeStartOfWeek =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_start_of_week d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeStartOfMonth =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_start_of_month d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeStartOfQuarter =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_start_of_quarter d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeStartOfYear =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_start_of_year d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeEndOfDay =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_end_of_day d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeEndOfWeek =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_end_of_week d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeEndOfMonth =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_end_of_month d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeEndOfQuarter =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_end_of_quarter d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeEndOfYear =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejforeign (enhanceddateTime d) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_end_of_year d)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeFormatFromString =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejstring s => Some (ejforeign (enhanceddateTimeformat (DATE_TIME_FORMAT_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeFromString =>
    apply_unary
      (fun d =>
         match d with
         | ejstring s => Some (ejforeign (enhanceddateTime (DATE_TIME_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeMax =>
    apply_unary
      (fun d =>
         match d with
         | ejarray jl =>
           match ejson_dates jl with
           | Some dl => Some (ejforeign (enhanceddateTime (DATE_TIME_max dl)))
           | None => None
           end
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeMin =>
    apply_unary
      (fun d =>
         match d with
         | ejarray jl =>
           match ejson_dates jl with
           | Some dl => Some (ejforeign (enhanceddateTime (DATE_TIME_min dl)))
           | None => None
           end
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationAmount =>
    apply_unary
      (fun d =>
         match d with
         | ejforeign (enhanceddateTimeduration fd) =>
           Some (ejbigint (DATE_TIME_DURATION_amount fd))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromString =>
    apply_unary
      (fun d =>
         match d with
         | ejstring s => Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromString =>
    apply_unary
      (fun d =>
         match d with
         | ejstring s => Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_string s)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromSeconds =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_seconds n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromMinutes =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_minutes n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromHours =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_hours n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromDays =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_days n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimeDurationFromWeeks =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_DURATION_from_weeks n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromDays =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_days n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromWeeks =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_weeks n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromMonths =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_months n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromQuarters =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_quarters n)))
         | _ => None
         end) dl
  | EJsonRuntimeDateTimePeriodFromYears =>
    apply_unary
      (fun d : ejson =>
         match d with
         | ejbigint n =>
           Some (ejforeign (enhanceddateTimeperiod (DATE_TIME_PERIOD_from_years n)))
         | _ => None
         end) dl
  (* Binary *)
  | EJsonRuntimeDateTimeFormat =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d), ejforeign (enhanceddateTimeformat f) =>
           Some (ejstring (DATE_TIME_format d f))
         | _, _ => None
       end) dl
  | EJsonRuntimeDateTimeAdd =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d), ejforeign (enhanceddateTimeduration du) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_add d du)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeSubtract =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d), ejforeign (enhanceddateTimeduration du) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_subtract d du)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeAddPeriod =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d), ejforeign (enhanceddateTimeperiod p) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_add_period d p)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeSubtractPeriod =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d), ejforeign (enhanceddateTimeperiod p) =>
           Some (ejforeign (enhanceddateTime (DATE_TIME_subtract_period d p)))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeIsSame =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d1), ejforeign (enhanceddateTime d2) =>
           Some (ejbool (DATE_TIME_eq d1 d2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeIsBefore =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d1), ejforeign (enhanceddateTime d2) =>
           Some (ejbool (DATE_TIME_is_before d1 d2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeIsAfter =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d1), ejforeign (enhanceddateTime d2) =>
           Some (ejbool (DATE_TIME_is_after d1 d2))
         | _, _ => None
         end) dl
  | EJsonRuntimeDateTimeDiff =>
    apply_binary
      (fun d1 d2 : ejson =>
         match d1, d2 with
         | ejforeign (enhanceddateTime d1), ejforeign (enhanceddateTime d2) =>
           Some (ejforeign (enhanceddateTimeduration (DATE_TIME_diff d1 d2)))
         | _, _ => None
         end) dl
  end.

Definition enhanced_foreign_ejson_runtime_op_interp op :=
  match op with
  | enhanced_ejson_uri sop =>
    enhanced_ejson_uri_runtime_op_interp sop
  | enhanced_ejson_log sop =>
    enhanced_ejson_log_runtime_op_interp sop
  | enhanced_ejson_math sop =>
    enhanced_ejson_math_runtime_op_interp sop
  | enhanced_ejson_date_time sop =>
    enhanced_ejson_date_time_runtime_op_interp sop
  end.

Section toString. (* XXX Maybe to move as a component ? *)
  Fixpoint ejsonEnumToString (b:brands) (j:ejson) : string :=
    match j with
    | ejobject ((s1,j)::nil) =>
      if (string_dec s1 "$left") then
        match j with
        | ejstring s =>
          append "~"
                 (append (@toString _ ToString_brands b)
                         (append "."
                                 (stringToString s)))
        | _ => "<BOGUS ENUM>"
        end
      else if (string_dec s1 "$right") then
             ejsonEnumToString b j
           else "<BOGUS ENUM>"
    | _ => "<BOGUS ENUM>"
    end.

  Definition ejsonLeftToString (j:string) : string :=
    string_bracket "Left("%string j ")"%string.
  Definition ejsonRightToString (j:string) : string :=
    string_bracket "Right("%string j ")"%string.
  Definition ejsonArrayToString (jl:list string) : string :=
    string_bracket "["%string (concat ", " jl) "]"%string.
  Definition ejsonObjectToString (jl:list (string * string)) : string :=
    string_bracket
      "{"%string
      (concat "," 
              (map (fun xy => (append (stringToString (key_decode (fst xy)))
                                      (append ":"%string (snd xy)))) jl))
      "}"%string.
  
  Fixpoint ejsonToString (j:ejson) : string :=
    match j with
    | ejnull => "unit"%string
    | ejbigint n => toString n
    | ejnumber n => toString n
    | ejbool b => toString b
    | ejstring s => string_bracket """"%string (stringToString s) """"%string
    | ejarray l => ejsonArrayToString (map ejsonToString l)
    | ejobject ((s1,j')::nil) =>
      if (string_dec s1 "$left") then ejsonLeftToString (ejsonToString j')
      else if (string_dec s1 "$right") then ejsonRightToString (ejsonToString j')
           else ejsonObjectToString ((s1,defaultEJsonToString j')::nil)
    | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
        if (string_dec s1 "$class") then
          if (string_dec s2 "$data") then
            match (ejson_brands j1) with
            | Some br =>
              match j2 with
              | ejobject ((s1,j')::nil) =>
                if (string_dec s1 "$left") then ejsonEnumToString br j'
                else if (string_dec s1 "$right") then ejsonEnumToString br j'
                     else
                       append "~"
                              (append (@toString _ ToString_brands br)
                                      (ejsonObjectToString ((s1,defaultEJsonToString j')::nil)))
              | ejobject ((s1,ejarray j1)::(s2,j2)::nil) =>
                if (string_dec s1 "$class") then
                  if (string_dec s2 "$data") then
                    match (ejson_brands j1) with
                    | Some br => "<BOGUS OBJECT>"
                    | _ =>
                      append "~"
                             (append (@toString _ ToString_brands br)
                                     (ejsonObjectToString
                                        ((s1,ejsonArrayToString (map ejsonToString j1))
                                           :: (s2, ejsonToString j2)
                                           :: nil)))
                    end
                  else
                      append "~"
                             (append (@toString _ ToString_brands br)
                                     (ejsonObjectToString
                                        ((s1,ejsonArrayToString (map ejsonToString j1))
                                           :: (s2, ejsonToString j2)
                                           :: nil)))
                  else
                      append "~"
                             (append (@toString _ ToString_brands br)
                                     (ejsonObjectToString
                                        ((s1,ejsonArrayToString (map ejsonToString j1))
                                           :: (s2, ejsonToString j2)
                                           :: nil)))
              | _ => "<BOGUS OBJECT>"
              end
            | None =>
              ejsonObjectToString
                ((s1,ejsonArrayToString (map ejsonToString j1))
                   :: (s2, ejsonToString j2)
                   :: nil)
            end
          else
            ejsonObjectToString
              ((s1,ejsonArrayToString (map ejsonToString j1))
                 :: (s2, ejsonToString j2)
                 :: nil)
        else
          ejsonObjectToString
            ((s1,ejsonArrayToString (map ejsonToString j1))
               :: (s2, ejsonToString j2)
               :: nil)
    | ejobject r =>
          ejsonObjectToString (map (fun xy => (fst xy, ejsonToString (snd xy))) r)
    | ejforeign fd => toString fd
    end.

  Definition ejsonToText (j:ejson) : string := ejsonToString j.

End toString.

Program Instance enhanced_foreign_ejson_runtime : foreign_ejson_runtime :=
  mk_foreign_ejson_runtime enhanced_foreign_ejson enhanced_foreign_ejson_runtime_op _ _ _ _ _.
Next Obligation.
  red; unfold equiv; intros.
  change ({x = y} + {x <> y}).
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
Defined.
Next Obligation.
  constructor; intros op.
  exact (enhanced_foreign_ejson_runtime_op_tostring op).
Defined.
Next Obligation.
  exact (enhanced_foreign_ejson_runtime_op_interp f dl).
Defined.
Next Obligation.
  exact (ejsonToString H).
Defined.
Next Obligation.
  exact (ejsonToText H).
Defined.

