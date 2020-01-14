
type json =
| Coq_jnull
| Coq_jnumber of float
| Coq_jbool of bool
| Coq_jstring of char list
| Coq_jarray of json list
| Coq_jobject of (char list * json) list
