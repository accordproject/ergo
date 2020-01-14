open ForeignData
open ForeignDataTyping
open ForeignType
open QcertData
open QcertType

(** val enhanced_infer_type : enhanced_data -> enhanced_type option **)

let enhanced_infer_type = function
| Coq_enhanceddateTimeformat _ -> Some Coq_enhancedDateTimeFormat
| Coq_enhanceddateTime _ -> Some Coq_enhancedDateTime
| Coq_enhanceddateTimeduration _ -> Some Coq_enhancedDateTimeDuration
| Coq_enhanceddateTimeperiod _ -> Some Coq_enhancedDateTimePeriod

(** val enhanced_foreign_data_typing_obligation_4 :
    foreign_data_model -> foreign_type_type **)

let enhanced_foreign_data_typing_obligation_4 d =
  match Obj.magic d with
  | Coq_enhanceddateTimeformat _ -> Obj.magic Coq_enhancedDateTimeFormat
  | Coq_enhanceddateTime _ -> Obj.magic Coq_enhancedDateTime
  | Coq_enhanceddateTimeduration _ -> Obj.magic Coq_enhancedDateTimeDuration
  | Coq_enhanceddateTimeperiod _ -> Obj.magic Coq_enhancedDateTimePeriod

(** val enhanced_foreign_data_typing : foreign_data_typing **)

let enhanced_foreign_data_typing =
  { foreign_data_typing_infer = (Obj.magic enhanced_infer_type);
    foreign_data_typing_infer_normalized = (fun d _ ->
    enhanced_foreign_data_typing_obligation_4 d) }
