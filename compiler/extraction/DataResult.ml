open Data
open ForeignData
open Result

type qerror =
| CompilationError of char list
| TypeError of char list
| UserError of data

type 'a qresult = ('a, qerror) coq_Result

(** val qsuccess : foreign_data -> 'a1 -> 'a1 qresult **)

let qsuccess _ a =
  Success a

(** val qfailure : foreign_data -> qerror -> 'a1 qresult **)

let qfailure _ e =
  Failure e
