open EquivDec
open ForeignType
open Lattice

type enhanced_type =
| Coq_enhancedTop
| Coq_enhancedBottom
| Coq_enhancedString
| Coq_enhancedDateTimeFormat
| Coq_enhancedDateTime
| Coq_enhancedDateTimeDuration
| Coq_enhancedDateTimePeriod

val enhanced_type_join : enhanced_type -> enhanced_type -> enhanced_type

val enhanced_type_meet : enhanced_type -> enhanced_type -> enhanced_type

val enhanced_type_lattice : enhanced_type coq_Lattice

val enhanced_foreign_type_obligation_1 : enhanced_type coq_EqDec

val enhanced_foreign_type_obligation_2 :
  enhanced_type -> enhanced_type -> bool

val enhanced_foreign_type : foreign_type
