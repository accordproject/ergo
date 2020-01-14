open JsNumber

type unary_op =
| Coq_unary_op_delete
| Coq_unary_op_void
| Coq_unary_op_typeof
| Coq_unary_op_post_incr
| Coq_unary_op_post_decr
| Coq_unary_op_pre_incr
| Coq_unary_op_pre_decr
| Coq_unary_op_add
| Coq_unary_op_neg
| Coq_unary_op_bitwise_not
| Coq_unary_op_not

type binary_op =
| Coq_binary_op_mult
| Coq_binary_op_div
| Coq_binary_op_mod
| Coq_binary_op_add
| Coq_binary_op_sub
| Coq_binary_op_left_shift
| Coq_binary_op_right_shift
| Coq_binary_op_unsigned_right_shift
| Coq_binary_op_lt
| Coq_binary_op_gt
| Coq_binary_op_le
| Coq_binary_op_ge
| Coq_binary_op_instanceof
| Coq_binary_op_in
| Coq_binary_op_equal
| Coq_binary_op_disequal
| Coq_binary_op_strict_equal
| Coq_binary_op_strict_disequal
| Coq_binary_op_bitwise_and
| Coq_binary_op_bitwise_or
| Coq_binary_op_bitwise_xor
| Coq_binary_op_and
| Coq_binary_op_or
| Coq_binary_op_coma

type literal =
| Coq_literal_null
| Coq_literal_bool of bool
| Coq_literal_number of number
| Coq_literal_string of char list

type label =
| Coq_label_empty
| Coq_label_string of char list

type label_set = label list

type strictness_flag = bool

val strictness_true : strictness_flag

type propname =
| Coq_propname_identifier of char list
| Coq_propname_string of char list
| Coq_propname_number of number

type expr =
| Coq_expr_this
| Coq_expr_identifier of char list
| Coq_expr_literal of literal
| Coq_expr_object of (propname * propbody) list
| Coq_expr_array of expr option list
| Coq_expr_function of char list option * char list list * funcbody
| Coq_expr_access of expr * expr
| Coq_expr_member of expr * char list
| Coq_expr_new of expr * expr list
| Coq_expr_call of expr * expr list
| Coq_expr_unary_op of unary_op * expr
| Coq_expr_binary_op of expr * binary_op * expr
| Coq_expr_conditional of expr * expr * expr
| Coq_expr_assign of expr * binary_op option * expr
and propbody =
| Coq_propbody_val of expr
| Coq_propbody_get of funcbody
| Coq_propbody_set of char list list * funcbody
and funcbody =
| Coq_funcbody_intro of prog * char list
and stat =
| Coq_stat_expr of expr
| Coq_stat_label of char list * stat
| Coq_stat_block of stat list
| Coq_stat_var_decl of (char list * expr option) list
| Coq_stat_let_decl of (char list * expr option) list
| Coq_stat_if of expr * stat * stat option
| Coq_stat_do_while of label_set * stat * expr
| Coq_stat_while of label_set * expr * stat
| Coq_stat_with of expr * stat
| Coq_stat_throw of expr
| Coq_stat_return of expr option
| Coq_stat_break of label
| Coq_stat_continue of label
| Coq_stat_try of stat * (char list * stat) option * stat option
| Coq_stat_for of label_set * expr option * expr option * expr option * stat
| Coq_stat_for_var of label_set * (char list * expr option) list
   * expr option * expr option * stat
| Coq_stat_for_let of label_set * (char list * expr option) list
   * expr option * expr option * stat
| Coq_stat_for_in of label_set * expr * expr * stat
| Coq_stat_for_in_var of label_set * char list * expr option * expr * stat
| Coq_stat_for_in_let of label_set * char list * expr option * expr * stat
| Coq_stat_debugger
| Coq_stat_switch of label_set * expr * switchbody
and switchbody =
| Coq_switchbody_nodefault of switchclause list
| Coq_switchbody_withdefault of switchclause list * stat list
   * switchclause list
and switchclause =
| Coq_switchclause_intro of expr * stat list
and prog =
| Coq_prog_intro of strictness_flag * element list
and element =
| Coq_element_stat of stat
| Coq_element_func_decl of char list * char list list * funcbody

type funcdecl = { funcdecl_name : char list;
                  funcdecl_parameters : char list list;
                  funcdecl_body : funcbody }
