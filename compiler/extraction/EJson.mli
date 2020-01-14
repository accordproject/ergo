
type 'foreign_ejson_model ejson =
| Coq_ejnull
| Coq_ejnumber of float
| Coq_ejbigint of int
| Coq_ejbool of bool
| Coq_ejstring of char list
| Coq_ejarray of 'foreign_ejson_model ejson list
| Coq_ejobject of (char list * 'foreign_ejson_model ejson) list
| Coq_ejforeign of 'foreign_ejson_model

val of_string_list : 'a1 ejson list -> char list list option

val ejson_brands : 'a1 ejson list -> char list list option

type 'foreign_ejson_model cejson =
| Coq_cejnull
| Coq_cejnumber of float
| Coq_cejbigint of int
| Coq_cejbool of bool
| Coq_cejstring of char list
| Coq_cejforeign of 'foreign_ejson_model
