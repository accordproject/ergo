
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val id : 'a1 -> 'a1

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : int -> int -> int

val sub : int -> int -> int

val bool_dec : bool -> bool -> bool

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

module Nat :
 sig
  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val div2 : int -> int

  val div2_up : int -> int

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask

  val sqrtrem : int -> int * mask

  val sqrt : int -> int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int

  val eq_dec : int -> int -> bool
 end

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val to_nat : int -> int

  val of_nat : int -> int
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> int

val n_of_ascii : char -> int

val nat_of_ascii : char -> int

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth_error : 'a1 list -> int -> 'a1 option

val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val sgn : int -> int

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int

  val abs : int -> int

  val to_nat : int -> int

  val of_nat : int -> int

  val of_N : int -> int

  val pos_div_eucl : int -> int -> int * int

  val quotrem : int -> int -> int * int

  val quot : int -> int -> int

  val rem : int -> int -> int

  val div2 : int -> int

  val log2 : int -> int

  val sqrt : int -> int

  val shiftl : int -> int -> int

  val eq_dec : int -> int -> bool
 end

val z_lt_dec : int -> int -> bool

val z_le_dec : int -> int -> bool

val string_dec : char list -> char list -> bool

val append : char list -> char list -> char list

val length0 : char list -> int

val substring : int -> int -> char list -> char list

val concat0 : char list -> char list list -> char list

val prefix : char list -> char list -> bool

val index : int -> char list -> char list -> int option

type nan_pl = int



type binary64 = float

type number = binary64



type 'a eqDec = 'a -> 'a -> bool

val equiv_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool

val equiv_decb : 'a1 eqDec -> 'a1 -> 'a1 -> bool

val nat_eq_eqdec : int eqDec

val unit_eqdec : unit eqDec

val list_eqdec : 'a1 eqDec -> 'a1 list eqDec

type float = binary64

val float_nan : float

val float_infinity : float

val float_neg_infinity : float

val float_to_string : float -> char list

val float_eq_dec : float eqDec

val float_list_min : float list -> float

val float_list_max : float list -> float

val float_list_sum : float list -> float

val float_list_arithmean : float list -> float

type digit = int

val nat_to_digits_backwards : int -> int -> digit list

val nat_to_digits : int -> int -> digit list

val digit_to_char : int -> digit -> char

val list_to_string : char list -> char list

val digits_to_string_aux : int -> digit list -> char list

val digits_to_string : int -> digit list -> char list

val nat_to_string : int -> int -> char list

val nat_to_string10 : int -> char list

val z_to_string10 : int -> char list

val nat_to_string16 : int -> char list

val forall_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool

val exists_in_dec : 'a1 list -> ('a1 -> __ -> bool) -> bool

type ('a, 'p) forallt =
| Forallt_nil
| Forallt_cons of 'a * 'a list * 'p * ('a, 'p) forallt

val list_Forallt_eq_dec :
  'a1 list -> 'a1 list -> ('a1, 'a1 -> bool) forallt -> bool

val forallt_impl :
  'a1 list -> ('a1, 'a2) forallt -> ('a1, 'a2 -> 'a3) forallt -> ('a1, 'a3)
  forallt

val forallt_weaken : ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a2) forallt

val forallt_In : 'a1 list -> 'a1 eqDec -> ('a1, 'a2) forallt -> 'a1 -> 'a2

val pair_eq_dec : 'a1 -> 'a2 -> 'a1 -> 'a2 -> bool -> bool -> bool

val string_eqdec : char list eqDec

val pair_eqdec : 'a1 eqDec -> 'a2 eqDec -> ('a1 * 'a2) eqDec

val option_eqdec : 'a1 eqDec -> 'a1 option eqDec

val zToSignedNat : int -> bool * int

val is_true : bool -> bool

type 'a toString =
  'a -> char list
  (* singleton inductive, whose constructor was Build_ToString *)

val toString0 : 'a1 toString -> 'a1 -> char list

module AsciiOrder :
 sig
  val compare : char -> char -> comparison
 end

module StringOrder :
 sig
  val compare : char list -> char list -> comparison

  val lt_dec : char list -> char list -> bool
 end

val map_string : (char -> char) -> char list -> char list

val ascii_dec : char eqDec

val map_concat : char list -> ('a1 -> char list) -> 'a1 list -> char list

val string_reverse_helper : char list -> char list -> char list

val string_reverse : char list -> char list

type like_clause =
| Like_literal of char list
| Like_any_char
| Like_any_string

val make_like_clause : char list -> char option -> like_clause list

val string_exists_suffix : (char list -> bool) -> char list -> bool

val like_clause_matches_string : like_clause list -> char list -> bool

val string_like : char list -> char list -> char option -> bool

type nstring = string

val nstring_quote : char list -> nstring

val nstring_append : nstring -> nstring -> nstring

val nstring_flat_map : (char -> nstring) -> nstring -> nstring

val nstring_concat : nstring -> nstring list -> nstring

val nstring_map_concat : nstring -> ('a1 -> nstring) -> 'a1 list -> nstring

val nstring_multi_append : nstring -> ('a1 -> nstring) -> 'a1 list -> nstring

val get_local_part : char list -> char list option

val find_duplicate : char list list -> char list option

val filter_some : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val postpend : 'a1 list -> 'a1 -> 'a1 list

val last_some_pair : ('a1 option * 'a2 option) list -> 'a1 option * 'a2 option

val coq_distinct : ('a1 -> char list) -> 'a1 list -> 'a1 list

val coq_toposort :
  ('a1 -> 'a2) -> ('a1 -> char list) -> ('a1 * 'a1 list) list -> 'a1 list

val coq_sort_given_topo_order :
  'a1 list -> ('a1 -> char list) -> ('a2 -> char list) -> ('a1 -> char list)
  -> 'a2 list -> 'a2 list

val coq_time : char list -> ('a1 -> 'a2) -> 'a1 -> 'a2

type 'a set = 'a list

val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val lift : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val olift : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val lift2 : ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option

val mk_lazy_lift :
  'a1 eqDec -> ('a2 -> 'a1 -> 'a1 -> 'a2) -> 'a2 -> 'a1 -> 'a1 -> 'a2

val forall_dec_defined : ('a1 -> bool) -> 'a1 list -> bool

val incl_list_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val noDup_dec : 'a1 eqDec -> 'a1 list -> bool

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option

val insertion_sort_insert :
  ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val insertion_sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val is_list_sorted : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

type 'a lattice = { meet : ('a -> 'a -> 'a); join : ('a -> 'a -> 'a) }

val meet : 'a1 lattice -> 'a1 -> 'a1 -> 'a1

val join : 'a1 lattice -> 'a1 -> 'a1 -> 'a1

val lookup : ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option

val update_first :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 -> ('a1 * 'a2) list

val domain : ('a1 * 'a2) list -> 'a1 list

val assoc_lookupr :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> 'a1 -> 'a2 option

val lookup_diff :
  ('a1 -> 'a1 -> bool) -> ('a1 * 'a2) list -> ('a1 * 'a3) list -> ('a1 * 'a2)
  list

val sublist_dec : 'a1 eqDec -> 'a1 list -> 'a1 list -> bool

val lift_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val lift_flat_map : ('a1 -> 'a2 list option) -> 'a1 list -> 'a2 list option

val compatible_with :
  'a1 eqDec -> 'a2 eqDec -> 'a1 -> 'a2 -> ('a1 * 'a2) list -> bool

val compatible :
  'a1 eqDec -> 'a2 eqDec -> ('a1 * 'a2) list -> ('a1 * 'a2) list -> bool

val find_bounded : ('a1 -> 'a1) -> ('a1 -> bool) -> int -> 'a1 -> 'a1 option

val find_bounded_S_nin_finds :
  (int -> 'a1) -> 'a1 eqDec -> 'a1 list -> int -> 'a1

val find_fresh_inj_f : 'a1 eqDec -> (int -> 'a1) -> 'a1 list -> 'a1

val find_fresh_string : char list list -> char list

val fresh_var : char list -> char list list -> char list

val fresh_var2 :
  char list -> char list -> char list list -> char list * char list

val get_var_base : char list -> char list -> char list

val fresh_var_from : char list -> char list -> char list list -> char list

type 'k oDT = { oDT_eqdec : 'k eqDec; oDT_lt_dec : ('k -> 'k -> bool);
                oDT_compare : ('k -> 'k -> comparison) }

val oDT_eqdec : 'a1 oDT -> 'a1 eqDec

val oDT_lt_dec : 'a1 oDT -> 'a1 -> 'a1 -> bool

val rec_field_lt_dec : 'a1 oDT -> ('a1 * 'a2) -> ('a1 * 'a2) -> bool

val rec_sort : 'a1 oDT -> ('a1 * 'a2) list -> ('a1 * 'a2) list

val rec_concat_sort :
  'a1 oDT -> ('a1 * 'a2) list -> ('a1 * 'a2) list -> ('a1 * 'a2) list

val oDT_string : char list oDT

val edot : (char list * 'a1) list -> char list -> 'a1 option

val merge_bindings :
  'a1 eqDec -> (char list * 'a1) list -> (char list * 'a1) list ->
  (char list * 'a1) list option

val rproject :
  (char list * 'a1) list -> char list list -> (char list * 'a1) list

val rremove : (char list * 'a1) list -> char list -> (char list * 'a1) list

val bunion : 'a1 list -> 'a1 list -> 'a1 list

val remove_one : 'a1 eqDec -> 'a1 -> 'a1 list -> 'a1 list

val bminus : 'a1 eqDec -> 'a1 list -> 'a1 list -> 'a1 list

val mult : 'a1 eqDec -> 'a1 list -> 'a1 -> int

val bmin : 'a1 eqDec -> 'a1 list -> 'a1 list -> 'a1 list

val bmax : 'a1 eqDec -> 'a1 list -> 'a1 list -> 'a1 list

val bcount : 'a1 list -> int

val bdistinct : 'a1 eqDec -> 'a1 list -> 'a1 list

val bnummin : int list -> int

val bnummax : int list -> int

type var = char list

type ('a, 'e) result =
| Success of 'a
| Failure of 'e

val lift_failure :
  ('a1 -> ('a2, 'a3) result) -> ('a1, 'a3) result -> ('a2, 'a3) result

val lift_failure_in : ('a1 -> 'a2) -> ('a1, 'a3) result -> ('a2, 'a3) result

val result_of_option : 'a1 option -> 'a2 -> ('a1, 'a2) result

val boolToString : bool -> char list

val stringToString : char list -> char list

val toString_Z : int toString

val toString_float : float toString

val toString_bool : bool toString

type sortDesc =
| Descending
| Ascending

type sortCriteria = char list * sortDesc

type sortCriterias = sortCriteria list

type sdata =
| Sdnat of int
| Sdstring of char list

module SortableDataOrder :
 sig
  type t = sdata

  val compare : t -> t -> comparison
 end

module LexicographicDataOrder :
 sig
  type t = sdata list

  val compare : sdata list -> sdata list -> comparison

  val le_dec : t -> t -> bool
 end

type 'a sortable_data = sdata list * 'a

type 'a sortable_coll = 'a sortable_data list

val dict_field_le_dec : 'a1 sortable_data -> 'a1 sortable_data -> bool

val dict_sort : (sdata list * 'a1) list -> (sdata list * 'a1) list

val sort_sortable_coll : 'a1 sortable_coll -> 'a1 sortable_coll

val coll_of_sortable_coll : 'a1 sortable_coll -> 'a1 list

val apply_unary : ('a1 -> 'a1 option) -> 'a1 list -> 'a1 option

val apply_binary : ('a1 -> 'a1 -> 'a1 option) -> 'a1 list -> 'a1 option

val eol_newline : char list

val neol_newline : nstring

val quotel_double : char list

val nquotel_double : nstring

val indent : int -> nstring

val string_bracket : char list -> char list -> char list -> char list

val nstring_bracket : nstring -> nstring -> nstring -> nstring

val jsAllowedIdentifierInitialCharacters : char list

val jsAllowedIdentifierCharacters : char list

val jsIdentifierInitialCharacterToAdd : char

val jsIdenitiferCharacterForReplacement : char

val jsIdentifierFixInitial : char list -> char list

val jsIdentifierSanitizeChar : char -> char

val jsIdentifierSanitizeBody : char list -> char list

val jsIdentifierSanitize : char list -> char list

val javaAllowedIdentifierInitialCharacters : char list

val javaAllowedIdentifierCharacters : char list

val javaIdentifierInitialCharacterToAdd : char

val javaIdenitiferCharacterForReplacement : char

val javaIdentifierFixInitial : char list -> char list

val javaIdentifierSanitizeChar : char -> char

val javaIdentifierSanitizeBody : char list -> char list

val javaIdentifierSanitize : char list -> char list

val javaSafeSeparator : char list

val javaAvoidList : char list list

val key_encode : char list -> char list

val key_decode : char list -> char list

type brand = char list

type brands = brand list

type brand_relation_t = (char list * char list) list

val brand_relation_trans_dec : brand_relation_t -> bool

val brand_relation_assym_dec : brand_relation_t -> bool

type brand_relation =
  (char list * char list) list
  (* singleton inductive, whose constructor was mkBrand_relation *)

val brand_relation_brands : brand_relation -> (char list * char list) list

val sub_brand_dec : brand_relation_t -> brand -> brand -> bool

val sub_brands_dec : brand_relation_t -> brands -> brands -> bool

val parents : brand_relation_t -> brand -> char list list

val parents_and_self : brand_relation_t -> brand -> brand list

val explode_brands : brand_relation_t -> brands -> brand list

val has_subtype_in : brand_relation_t -> brands -> brand -> bool

val collapse_brands : brand_relation_t -> brands -> brand list

val canon_brands : brand_relation_t -> brands -> char list list

val is_canon_brands_dec : brand_relation_t -> brands -> bool

val brand_join : brand_relation_t -> brands -> brands -> char list list

val brand_meet : brand_relation_t -> brands -> brands -> char list list

val ergo_version : char list

type foreign_data = { foreign_data_dec : __ eqDec;
                      foreign_data_normalize : (__ -> __);
                      foreign_data_tostring : __ toString }

type foreign_data_model = __

val foreign_data_dec : foreign_data -> foreign_data_model eqDec

val foreign_data_normalize :
  foreign_data -> foreign_data_model -> foreign_data_model

val foreign_data_tostring : foreign_data -> foreign_data_model toString

module Coq__4 : sig
 type data =
 | Dunit
 | Dnat of int
 | Dfloat of float
 | Dbool of bool
 | Dstring of char list
 | Dcoll of data list
 | Drec of (char list * data) list
 | Dleft of data
 | Dright of data
 | Dbrand of brands * data
 | Dforeign of foreign_data_model
end
include module type of struct include Coq__4 end

val data_eq_dec : foreign_data -> data -> data -> bool

val data_eqdec : foreign_data -> data eqDec

val dsome : foreign_data -> data -> data

val dnone : foreign_data -> data

val normalize_data : foreign_data -> brand_relation_t -> data -> data

type foreign_operators = { foreign_operators_unary_dec : __ eqDec;
                           foreign_operators_unary_tostring : __ toString;
                           foreign_operators_unary_interp : (brand_relation_t
                                                            -> __ -> data ->
                                                            data option);
                           foreign_operators_binary_dec : __ eqDec;
                           foreign_operators_binary_tostring : __ toString;
                           foreign_operators_binary_interp : (brand_relation_t
                                                             -> __ -> data ->
                                                             data -> data
                                                             option);
                           foreign_operators_unary_data_tostring : (data ->
                                                                   char list);
                           foreign_operators_unary_data_totext : (data ->
                                                                 char list) }

type foreign_operators_unary = __

val foreign_operators_unary_tostring :
  foreign_data -> foreign_operators -> foreign_operators_unary toString

val foreign_operators_unary_interp :
  foreign_data -> foreign_operators -> brand_relation_t ->
  foreign_operators_unary -> data -> data option

type foreign_operators_binary = __

val foreign_operators_binary_tostring :
  foreign_data -> foreign_operators -> foreign_operators_binary toString

val foreign_operators_binary_interp :
  foreign_data -> foreign_operators -> brand_relation_t ->
  foreign_operators_binary -> data -> data -> data option

val foreign_operators_unary_data_tostring :
  foreign_data -> foreign_operators -> data -> char list

val foreign_operators_unary_data_totext :
  foreign_data -> foreign_operators -> data -> char list

type foreign_runtime = { foreign_runtime_data : foreign_data;
                         foreign_runtime_operators : foreign_operators }

val foreign_runtime_data : foreign_runtime -> foreign_data

type qerror =
| CompilationError of char list
| TypeError of char list
| UserError of data

type 'a qresult = ('a, qerror) result

val qsuccess : foreign_data -> 'a1 -> 'a1 qresult

val qfailure : foreign_data -> qerror -> 'a1 qresult

val unbdbool :
  foreign_data -> (bool -> bool -> bool) -> data -> data -> data option

val unudbool : foreign_data -> (bool -> bool) -> data -> data option

val unbdnat :
  foreign_data -> (int -> int -> bool) -> data -> data -> data option

val unbdata :
  foreign_data -> (data -> data -> bool) -> data -> data -> data option

val unndstring : foreign_data -> (char list -> int) -> data -> data option

val unsdstring :
  foreign_data -> (char list -> char list -> char list) -> data -> data ->
  data option

val ondcoll2 :
  foreign_data -> (data list -> data list -> 'a1) -> data -> data -> 'a1
  option

val rondcoll2 :
  foreign_data -> (data list -> data list -> data list) -> data -> data ->
  data option

val ondstring : foreign_data -> (char list -> 'a1) -> data -> 'a1 option

val ondnat : foreign_data -> (int -> 'a1) -> data -> 'a1 option

val ondfloat : foreign_data -> (float -> 'a1) -> data -> 'a1 option

val ondcoll : foreign_data -> (data list -> 'a1) -> data -> 'a1 option

val lift_oncoll :
  foreign_data -> (data list -> 'a1 option) -> data -> 'a1 option

val rondcoll : foreign_data -> (data list -> data list) -> data -> data option

val oflatten : foreign_data -> data list -> data list option

val get_criteria : foreign_data -> data -> sortCriteria -> sdata option

val get_criterias : foreign_data -> data -> sortCriterias -> sdata list option

val sortable_data_of_data :
  foreign_data -> data -> sortCriterias -> data sortable_data option

val sortable_coll_of_coll :
  foreign_data -> sortCriterias -> data list -> data sortable_data list option

val data_sort : foreign_data -> sortCriterias -> data -> data option

val toString_brands : brands toString

val dsum : foreign_data -> data list -> int option

val darithmean : foreign_data -> data list -> int option

val lifted_stringbag : foreign_data -> data list -> char list list option

val lifted_zbag : foreign_data -> data list -> int list option

val lifted_min : foreign_data -> data list -> data option

val lifted_max : foreign_data -> data list -> data option

val lifted_fbag : foreign_data -> data list -> float list option

val lifted_fsum : foreign_data -> data list -> data option

val lifted_farithmean : foreign_data -> data list -> data option

val lifted_fmin : foreign_data -> data list -> data option

val lifted_fmax : foreign_data -> data list -> data option

val lifted_join : foreign_data -> char list -> data list -> data option

type nat_arith_unary_op =
| NatAbs
| NatLog2
| NatSqrt

type float_arith_unary_op =
| FloatNeg
| FloatSqrt
| FloatExp
| FloatLog
| FloatLog10
| FloatCeil
| FloatFloor
| FloatAbs

type unary_op =
| OpIdentity
| OpNeg
| OpRec of char list
| OpDot of char list
| OpRecRemove of char list
| OpRecProject of char list list
| OpBag
| OpSingleton
| OpFlatten
| OpDistinct
| OpOrderBy of sortCriterias
| OpCount
| OpToString
| OpToText
| OpLength
| OpSubstring of int * int option
| OpLike of char list
| OpLeft
| OpRight
| OpBrand of brands
| OpUnbrand
| OpCast of brands
| OpNatUnary of nat_arith_unary_op
| OpNatSum
| OpNatMin
| OpNatMax
| OpNatMean
| OpFloatOfNat
| OpFloatUnary of float_arith_unary_op
| OpFloatTruncate
| OpFloatSum
| OpFloatMean
| OpFloatBagMin
| OpFloatBagMax
| OpForeignUnary of foreign_operators_unary

val toString_nat_arith_unary_op : nat_arith_unary_op toString

val toString_float_arith_unary_op : float_arith_unary_op toString

val toString_SortDesc : sortDesc -> char list

val toString_SortCriteria : (char list * sortDesc) -> char list

val toString_unary_op : foreign_data -> foreign_operators -> unary_op toString

type nat_arith_binary_op =
| NatPlus
| NatMinus
| NatMult
| NatDiv
| NatRem
| NatMin
| NatMax

type float_arith_binary_op =
| FloatPlus
| FloatMinus
| FloatMult
| FloatDiv
| FloatPow
| FloatMin
| FloatMax

type float_compare_binary_op =
| FloatLt
| FloatLe
| FloatGt
| FloatGe

type binary_op =
| OpEqual
| OpRecConcat
| OpRecMerge
| OpAnd
| OpOr
| OpLt
| OpLe
| OpBagUnion
| OpBagDiff
| OpBagMin
| OpBagMax
| OpBagNth
| OpContains
| OpStringConcat
| OpStringJoin
| OpNatBinary of nat_arith_binary_op
| OpFloatBinary of float_arith_binary_op
| OpFloatCompare of float_compare_binary_op
| OpForeignBinary of foreign_operators_binary

val toString_nat_binary_op : nat_arith_binary_op toString

val toString_float_arith_binary_op : float_arith_binary_op toString

val toString_float_compare_binary_op : float_compare_binary_op toString

val toString_binary_op :
  foreign_data -> foreign_operators -> binary_op toString

val nat_arith_unary_op_eval : nat_arith_unary_op -> int -> int

val float_arith_unary_op_eval : float_arith_unary_op -> float -> float

val toString_data : foreign_data -> foreign_operators -> data toString

val unary_op_eval :
  foreign_data -> brand_relation_t -> foreign_operators -> unary_op -> data
  -> data option

val nat_arith_binary_op_eval : nat_arith_binary_op -> int -> int -> int

val float_arith_binary_op_eval :
  float_arith_binary_op -> float -> float -> float

val float_compare_binary_op_eval :
  float_compare_binary_op -> float -> float -> bool

val binary_op_eval :
  brand_relation_t -> foreign_data -> foreign_operators -> binary_op -> data
  -> data -> data option

type foreign_type = { foreign_type_dec : __ eqDec;
                      foreign_type_lattice : __ lattice;
                      foreign_type_sub_dec : (__ -> __ -> bool) }

type foreign_type_type = __

val foreign_type_dec : foreign_type -> foreign_type_type eqDec

val foreign_type_lattice : foreign_type -> foreign_type_type lattice

val foreign_type_sub_dec :
  foreign_type -> foreign_type_type -> foreign_type_type -> bool

module Coq__2 : sig
 type record_kind =
 | Open
 | Closed
end
include module type of struct include Coq__2 end

val record_kind_eqdec : record_kind eqDec

type rtype_UU2080_ =
| Bottom_UU2080_
| Top_UU2080_
| Unit_UU2080_
| Nat_UU2080_
| Float_UU2080_
| Bool_UU2080_
| String_UU2080_
| Coll_UU2080_ of rtype_UU2080_
| Rec_UU2080_ of record_kind * (char list * rtype_UU2080_) list
| Either_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Arrow_UU2080_ of rtype_UU2080_ * rtype_UU2080_
| Brand_UU2080_ of brands
| Foreign_UU2080_ of foreign_type_type

val rtype_UU2080__eqdec : foreign_type -> rtype_UU2080_ eqDec

type rtype = rtype_UU2080_

val rtype_eq_dec : foreign_type -> brand_relation -> rtype eqDec

val bottom : foreign_type -> brand_relation -> rtype

val top : foreign_type -> brand_relation -> rtype

val unit0 : foreign_type -> brand_relation -> rtype

val nat : foreign_type -> brand_relation -> rtype

val float0 : foreign_type -> brand_relation -> rtype

val bool : foreign_type -> brand_relation -> rtype

val string : foreign_type -> brand_relation -> rtype

val coll : foreign_type -> brand_relation -> rtype -> rtype

val either : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val arrow : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val foreign : foreign_type -> brand_relation -> foreign_type_type -> rtype

val rec0 :
  foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
  -> rtype

val brand0 : foreign_type -> brand_relation -> brands -> rtype

val option : foreign_type -> brand_relation -> rtype -> rtype

val from_Rec_UU2080_ :
  foreign_type -> brand_relation -> record_kind ->
  (char list * rtype_UU2080_) list -> (char list * rtype_UU2080_) list

val recMaybe :
  foreign_type -> brand_relation -> record_kind -> (char list * rtype) list
  -> rtype option

val record_kind_rtype_join :
  record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a1)
  list -> record_kind

val rtype_meet_compatible_records_dec :
  record_kind -> record_kind -> (char list * 'a1) list -> (char list * 'a2)
  list -> bool

val record_kind_rtype_meet : record_kind -> record_kind -> record_kind

val rtype_join_UU2080_ :
  foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
  rtype_UU2080_

val rtype_meet_UU2080_ :
  foreign_type -> brand_relation -> rtype_UU2080_ -> rtype_UU2080_ ->
  rtype_UU2080_

val rtype_join : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val rtype_meet : foreign_type -> brand_relation -> rtype -> rtype -> rtype

val subtype_both_dec :
  foreign_type -> brand_relation -> rtype -> rtype -> bool * bool

val subtype_dec : foreign_type -> brand_relation -> rtype -> rtype -> bool

val check_subtype_pairs :
  foreign_type -> brand_relation -> (rtype * rtype) list -> bool

val enforce_unary_op_schema :
  foreign_type -> brand_relation -> (rtype * rtype) -> rtype ->
  (rtype * rtype) option

val enforce_binary_op_schema :
  foreign_type -> brand_relation -> (rtype * rtype) -> (rtype * rtype) ->
  rtype -> ((rtype * rtype) * rtype) option

type brand_context_decls = (char list * rtype) list

type brand_context =
  brand_context_decls
  (* singleton inductive, whose constructor was mkBrand_context *)

val brand_context_types :
  foreign_type -> brand_relation -> brand_context -> brand_context_decls

val brand_model_domain_dec :
  foreign_type -> brand_relation -> brand_context -> bool

val brand_model_subtype_weak_dec :
  foreign_type -> brand_relation -> brand_context -> bool

type brand_model = { brand_model_relation : brand_relation;
                     brand_model_context : brand_context }

val brand_model_relation : foreign_type -> brand_model -> brand_relation

val brand_model_context : foreign_type -> brand_model -> brand_context

val make_brand_model :
  foreign_type -> brand_relation -> brand_context -> brand_model

val empty_brand_model : foreign_type -> brand_model

val rtype_lattice : foreign_type -> brand_relation -> rtype lattice

val brands_type_list : foreign_type -> brand_model -> brands -> rtype list

val brands_type : foreign_type -> brand_model -> brands -> rtype

type foreign_data_typing = { foreign_data_typing_infer : (foreign_data_model
                                                         -> foreign_type_type
                                                         option);
                             foreign_data_typing_infer_normalized : (foreign_data_model
                                                                    -> __ ->
                                                                    foreign_type_type) }

val foreign_data_typing_infer :
  foreign_data -> foreign_type -> foreign_data_typing -> foreign_data_model
  -> foreign_type_type option

val infer_data_type :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model -> data
  -> rtype option

val tdot : (char list * 'a1) list -> char list -> 'a1 option

val tuneither : foreign_type -> brand_model -> rtype -> (rtype * rtype) option

val tuncoll : foreign_type -> brand_model -> rtype -> rtype option

val tsingleton : foreign_type -> brand_model -> rtype -> rtype option

val tunrec :
  foreign_type -> brand_model -> rtype -> (record_kind * (char list * rtype)
  list) option

val trecConcatRight :
  foreign_type -> brand_model -> rtype -> rtype -> rtype option

val tmergeConcat :
  foreign_type -> brand_model -> rtype -> rtype -> rtype option

val tunrecdot :
  foreign_type -> brand_model -> char list -> rtype -> rtype option

val tunrecremove :
  foreign_type -> brand_model -> char list -> rtype -> rtype option

val tunrecproject :
  foreign_type -> brand_model -> char list list -> rtype -> rtype option

val sortable_type_dec : foreign_type -> brand_model -> rtype -> bool

val order_by_has_sortable_type_dec :
  foreign_type -> brand_model -> (char list * rtype) list -> char list list
  -> bool

type foreign_operators_typing = { foreign_operators_typing_unary_infer : 
                                  (foreign_operators_unary -> rtype -> rtype
                                  option);
                                  foreign_operators_typing_unary_infer_sub : 
                                  (foreign_operators_unary -> rtype ->
                                  (rtype * rtype) option);
                                  foreign_operators_typing_binary_infer : 
                                  (foreign_operators_binary -> rtype -> rtype
                                  -> rtype option);
                                  foreign_operators_typing_binary_infer_sub : 
                                  (foreign_operators_binary -> rtype -> rtype
                                  -> ((rtype * rtype) * rtype) option) }

val foreign_operators_typing_unary_infer_sub :
  foreign_data -> foreign_operators -> foreign_type -> foreign_data_typing ->
  brand_model -> foreign_operators_typing -> foreign_operators_unary -> rtype
  -> (rtype * rtype) option

val foreign_operators_typing_binary_infer_sub :
  foreign_data -> foreign_operators -> foreign_type -> foreign_data_typing ->
  brand_model -> foreign_operators_typing -> foreign_operators_binary ->
  rtype -> rtype -> ((rtype * rtype) * rtype) option

val tunrecsortable :
  foreign_type -> brand_model -> char list list -> rtype -> rtype option

val infer_binary_op_type_sub :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
  foreign_operators -> foreign_operators_typing -> binary_op -> rtype ->
  rtype -> ((rtype * rtype) * rtype) option

val infer_unary_op_type_sub :
  foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
  foreign_operators -> foreign_operators_typing -> unary_op -> rtype ->
  (rtype * rtype) option

type foreign_typing = { foreign_typing_data : foreign_data_typing;
                        foreign_typing_operators : foreign_operators_typing }

val mk_brand_relation :
  foreign_data -> (char list * char list) list -> brand_relation qresult

val mk_brand_context :
  foreign_type -> brand_relation -> brand_context_decls -> brand_context

val make_brand_model_from_decls_fails :
  foreign_data -> foreign_type -> brand_relation -> brand_context_decls ->
  brand_model qresult

type basic_model = { basic_model_runtime : foreign_runtime;
                     basic_model_foreign_type : foreign_type;
                     basic_model_brand_model : brand_model;
                     basic_model_foreign_typing : foreign_typing }

module Coq__3 : sig
 type json =
 | Jnull
 | Jnumber of float
 | Jbool of bool
 | Jstring of char list
 | Jarray of json list
 | Jobject of (char list * json) list
end
include module type of struct include Coq__3 end

type foreign_ejson = { foreign_ejson_dec : __ eqDec;
                       foreign_ejson_normalize : (__ -> __);
                       foreign_ejson_tostring : __ toString }

type foreign_ejson_model = __

val foreign_ejson_tostring : foreign_ejson -> foreign_ejson_model toString

type ejson =
| Ejnull
| Ejnumber of float
| Ejbigint of int
| Ejbool of bool
| Ejstring of char list
| Ejarray of ejson list
| Ejobject of (char list * ejson) list
| Ejforeign of foreign_ejson_model

val of_string_list : foreign_ejson -> ejson list -> char list list option

val ejson_brands : foreign_ejson -> ejson list -> char list list option

type foreign_ejson_runtime = { foreign_ejson_runtime_op_dec : __ eqDec;
                               foreign_ejson_runtime_op_tostring : __ toString;
                               foreign_ejson_runtime_op_interp : (__ -> ejson
                                                                 list ->
                                                                 ejson option);
                               foreign_ejson_runtime_tostring : (ejson ->
                                                                char list);
                               foreign_ejson_runtime_totext : (ejson ->
                                                              char list) }

type foreign_ejson_runtime_op = __

val foreign_ejson_runtime_op_tostring :
  foreign_ejson -> foreign_ejson_runtime -> foreign_ejson_runtime_op toString

type ejson_op =
| EJsonOpNot
| EJsonOpNeg
| EJsonOpAnd
| EJsonOpOr
| EJsonOpLt
| EJsonOpLe
| EJsonOpGt
| EJsonOpGe
| EJsonOpAddString
| EJsonOpAddNumber
| EJsonOpSub
| EJsonOpMult
| EJsonOpDiv
| EJsonOpStrictEqual
| EJsonOpStrictDisequal
| EJsonOpArray
| EJsonOpArrayLength
| EJsonOpArrayPush
| EJsonOpArrayAccess
| EJsonOpObject of char list list
| EJsonOpAccess of char list
| EJsonOpHasOwnProperty of char list
| EJsonOpMathMin
| EJsonOpMathMax
| EJsonOpMathMinApply
| EJsonOpMathMaxApply
| EJsonOpMathPow
| EJsonOpMathExp
| EJsonOpMathAbs
| EJsonOpMathLog
| EJsonOpMathLog10
| EJsonOpMathSqrt
| EJsonOpMathCeil
| EJsonOpMathFloor
| EJsonOpMathTrunc

type ejson_runtime_op =
| EJsonRuntimeEqual
| EJsonRuntimeCompare
| EJsonRuntimeToString
| EJsonRuntimeToText
| EJsonRuntimeRecConcat
| EJsonRuntimeRecMerge
| EJsonRuntimeRecRemove
| EJsonRuntimeRecProject
| EJsonRuntimeRecDot
| EJsonRuntimeEither
| EJsonRuntimeToLeft
| EJsonRuntimeToRight
| EJsonRuntimeBrand
| EJsonRuntimeUnbrand
| EJsonRuntimeCast
| EJsonRuntimeDistinct
| EJsonRuntimeSingleton
| EJsonRuntimeFlatten
| EJsonRuntimeUnion
| EJsonRuntimeMinus
| EJsonRuntimeMin
| EJsonRuntimeMax
| EJsonRuntimeNth
| EJsonRuntimeCount
| EJsonRuntimeContains
| EJsonRuntimeSort
| EJsonRuntimeGroupBy
| EJsonRuntimeLength
| EJsonRuntimeSubstring
| EJsonRuntimeSubstringEnd
| EJsonRuntimeStringJoin
| EJsonRuntimeLike
| EJsonRuntimeNatLt
| EJsonRuntimeNatLe
| EJsonRuntimeNatPlus
| EJsonRuntimeNatMinus
| EJsonRuntimeNatMult
| EJsonRuntimeNatDiv
| EJsonRuntimeNatRem
| EJsonRuntimeNatAbs
| EJsonRuntimeNatLog2
| EJsonRuntimeNatSqrt
| EJsonRuntimeNatMinPair
| EJsonRuntimeNatMaxPair
| EJsonRuntimeNatSum
| EJsonRuntimeNatMin
| EJsonRuntimeNatMax
| EJsonRuntimeNatArithMean
| EJsonRuntimeFloatOfNat
| EJsonRuntimeFloatSum
| EJsonRuntimeFloatArithMean
| EJsonRuntimeNatOfFloat
| EJsonRuntimeForeign of foreign_ejson_runtime_op

val string_of_ejson_runtime_op :
  foreign_ejson -> foreign_ejson_runtime -> ejson_runtime_op -> char list

val defaultEJsonToString : foreign_ejson -> ejson -> char list

type foreign_to_ejson = { foreign_to_ejson_runtime : foreign_ejson_runtime;
                          foreign_to_ejson_to_data : (foreign_ejson_model ->
                                                     foreign_data_model);
                          foreign_to_ejson_from_data : (foreign_data_model ->
                                                       foreign_ejson_model) }

val foreign_to_ejson_runtime :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime

val foreign_to_ejson_from_data :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson -> foreign_data_model
  -> foreign_ejson_model

type java = nstring

type java_json =
  nstring
  (* singleton inductive, whose constructor was mk_java_json *)

val from_java_json : java_json -> nstring

val mk_java_json_array : java_json list -> java_json

val mk_java_json_object : nstring -> (nstring * java_json) list -> java_json

val mk_java_json_primitive : nstring -> java_json

val mk_java_json_string : nstring -> nstring -> java_json

val java_json_NULL : java_json

val mk_java_json_nat : nstring -> int -> java_json

val mk_java_json_number : float -> java_json

val mk_java_json_bool : bool -> java_json

val mk_java_string : nstring -> nstring

val mk_java_call : nstring -> nstring -> java_json list -> java_json

val mk_java_unary_op0 : nstring -> java_json -> java_json

val mk_java_unary_op1 : nstring -> nstring -> java_json -> java_json

val mk_java_unary_opn : nstring -> nstring list -> java_json -> java_json

val mk_java_binary_op0 : nstring -> java_json -> java_json -> java_json

val mk_java_unary_op0_foreign : nstring -> nstring -> java_json -> java_json

val mk_java_binary_op0_foreign :
  nstring -> nstring -> java_json -> java_json -> java_json

val mk_java_collection : nstring -> nstring list -> nstring

val mk_java_string_collection : nstring list -> nstring

type foreign_to_java = { foreign_to_java_data : (nstring ->
                                                foreign_data_model ->
                                                java_json);
                         foreign_to_java_unary_op : (int -> nstring ->
                                                    nstring ->
                                                    foreign_operators_unary
                                                    -> java_json -> java_json);
                         foreign_to_java_binary_op : (int -> nstring ->
                                                     nstring ->
                                                     foreign_operators_binary
                                                     -> java_json ->
                                                     java_json -> java_json) }

val foreign_to_java_data :
  foreign_runtime -> foreign_to_java -> nstring -> foreign_data_model ->
  java_json

val foreign_to_java_unary_op :
  foreign_runtime -> foreign_to_java -> int -> nstring -> nstring ->
  foreign_operators_unary -> java_json -> java_json

val foreign_to_java_binary_op :
  foreign_runtime -> foreign_to_java -> int -> nstring -> nstring ->
  foreign_operators_binary -> java_json -> java_json -> java_json

type unary_op0 =
| Unary_op_delete
| Unary_op_void
| Unary_op_typeof
| Unary_op_post_incr
| Unary_op_post_decr
| Unary_op_pre_incr
| Unary_op_pre_decr
| Unary_op_add
| Unary_op_neg
| Unary_op_bitwise_not
| Unary_op_not

type binary_op0 =
| Binary_op_mult
| Binary_op_div
| Binary_op_mod
| Binary_op_add
| Binary_op_sub
| Binary_op_left_shift
| Binary_op_right_shift
| Binary_op_unsigned_right_shift
| Binary_op_lt
| Binary_op_gt
| Binary_op_le
| Binary_op_ge
| Binary_op_instanceof
| Binary_op_in
| Binary_op_equal
| Binary_op_disequal
| Binary_op_strict_equal
| Binary_op_strict_disequal
| Binary_op_bitwise_and
| Binary_op_bitwise_or
| Binary_op_bitwise_xor
| Binary_op_and
| Binary_op_or
| Binary_op_coma

type literal =
| Literal_null
| Literal_bool of bool
| Literal_number of number
| Literal_string of char list

type label =
| Label_empty
| Label_string of char list

type label_set = label list

type strictness_flag = bool

val strictness_true : strictness_flag

type propname =
| Propname_identifier of char list
| Propname_string of char list
| Propname_number of number

type expr =
| Expr_this
| Expr_identifier of char list
| Expr_literal of literal
| Expr_object of (propname * propbody) list
| Expr_array of expr option list
| Expr_function of char list option * char list list * funcbody
| Expr_access of expr * expr
| Expr_member of expr * char list
| Expr_new of expr * expr list
| Expr_call of expr * expr list
| Expr_unary_op of unary_op0 * expr
| Expr_binary_op of expr * binary_op0 * expr
| Expr_conditional of expr * expr * expr
| Expr_assign of expr * binary_op0 option * expr
and propbody =
| Propbody_val of expr
| Propbody_get of funcbody
| Propbody_set of char list list * funcbody
and funcbody =
| Funcbody_intro of prog * char list
and stat =
| Stat_expr of expr
| Stat_label of char list * stat
| Stat_block of stat list
| Stat_var_decl of (char list * expr option) list
| Stat_let_decl of (char list * expr option) list
| Stat_if of expr * stat * stat option
| Stat_do_while of label_set * stat * expr
| Stat_while of label_set * expr * stat
| Stat_with of expr * stat
| Stat_throw of expr
| Stat_return of expr option
| Stat_break of label
| Stat_continue of label
| Stat_try of stat * (char list * stat) option * stat option
| Stat_for of label_set * expr option * expr option * expr option * stat
| Stat_for_var of label_set * (char list * expr option) list * expr option
   * expr option * stat
| Stat_for_let of label_set * (char list * expr option) list * expr option
   * expr option * stat
| Stat_for_in of label_set * expr * expr * stat
| Stat_for_in_var of label_set * char list * expr option * expr * stat
| Stat_for_in_let of label_set * char list * expr option * expr * stat
| Stat_debugger
| Stat_switch of label_set * expr * switchbody
and switchbody =
| Switchbody_nodefault of switchclause list
| Switchbody_withdefault of switchclause list * stat list * switchclause list
and switchclause =
| Switchclause_intro of expr * stat list
and prog =
| Prog_intro of strictness_flag * element list
and element =
| Element_stat of stat
| Element_func_decl of char list * char list list * funcbody

type funcdecl = { funcdecl_name : char list;
                  funcdecl_parameters : char list list;
                  funcdecl_body : funcbody }

val funcdecl_name : funcdecl -> char list

val funcdecl_parameters : funcdecl -> char list list

val funcdecl_body : funcdecl -> funcbody

type topdecl =
| Strictmode
| Comment of char list
| Elementdecl of element
| Classdecl of char list * funcdecl list
| Constdecl of char list * expr

type js_ast = topdecl list

type foreign_ejson_to_ajavascript =
  foreign_ejson_model -> expr
  (* singleton inductive, whose constructor was mk_foreign_ejson_to_ajavascript *)

val foreign_ejson_to_ajavascript_expr :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_model -> expr

val data_to_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson -> data -> ejson

val sortCriteria_to_ejson : foreign_ejson -> (char list * sortDesc) -> ejson

type foreign_to_ejson_runtime0 = { foreign_to_ejson_runtime_of_unary_op : 
                                   (foreign_operators_unary ->
                                   foreign_ejson_runtime_op);
                                   foreign_to_ejson_runtime_of_binary_op : 
                                   (foreign_operators_binary ->
                                   foreign_ejson_runtime_op) }

val foreign_to_ejson_runtime_of_unary_op :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 ->
  foreign_operators_unary -> foreign_ejson_runtime_op

val foreign_to_ejson_runtime_of_binary_op :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 ->
  foreign_operators_binary -> foreign_ejson_runtime_op

type nnrc =
| NNRCGetConstant of var
| NNRCVar of var
| NNRCConst of data
| NNRCBinop of binary_op * nnrc * nnrc
| NNRCUnop of unary_op * nnrc
| NNRCLet of var * nnrc * nnrc
| NNRCFor of var * nnrc * nnrc
| NNRCIf of nnrc * nnrc * nnrc
| NNRCEither of nnrc * var * nnrc * var * nnrc
| NNRCGroupBy of char list * char list list * nnrc

val nnrc_global_vars : foreign_runtime -> nnrc -> var list

val nnrc_bound_vars : foreign_runtime -> nnrc -> var list

val nnrc_free_vars : foreign_runtime -> nnrc -> var list

val nnrc_subst : foreign_runtime -> nnrc -> var -> nnrc -> nnrc

val really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list

val pick_new_really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list

val pick_same_really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list

val nnrc_rename_lazy : foreign_runtime -> nnrc -> var -> var -> nnrc

val nnrc_pick_name :
  foreign_runtime -> char list -> (char list -> char list) -> var list -> var
  -> nnrc -> char list

val unshadow :
  foreign_runtime -> char list -> (char list -> char list) -> var list ->
  nnrc -> nnrc

val nnrc_subst_const_to_var :
  foreign_runtime -> char list list -> nnrc -> nnrc

val closeFreeVars :
  foreign_runtime -> char list -> (char list -> char list) -> nnrc -> nnrc ->
  char list list -> nnrc

type nnrs_imp_expr =
| NNRSimpGetConstant of var
| NNRSimpVar of var
| NNRSimpConst of data
| NNRSimpBinop of binary_op * nnrs_imp_expr * nnrs_imp_expr
| NNRSimpUnop of unary_op * nnrs_imp_expr
| NNRSimpGroupBy of char list * char list list * nnrs_imp_expr

type nnrs_imp_stmt =
| NNRSimpSkip
| NNRSimpSeq of nnrs_imp_stmt * nnrs_imp_stmt
| NNRSimpAssign of var * nnrs_imp_expr
| NNRSimpLet of var * nnrs_imp_expr option * nnrs_imp_stmt
| NNRSimpFor of var * nnrs_imp_expr * nnrs_imp_stmt
| NNRSimpIf of nnrs_imp_expr * nnrs_imp_stmt * nnrs_imp_stmt
| NNRSimpEither of nnrs_imp_expr * var * nnrs_imp_stmt * var * nnrs_imp_stmt

type nnrs_imp = nnrs_imp_stmt * var

type var0 = char list

type uri_unary_op =
| Uop_uri_encode
| Uop_uri_decode

val uri_unary_op_tostring : uri_unary_op -> char list

val cname : nstring

val uri_to_java_unary_op :
  int -> nstring -> nstring -> uri_unary_op -> java_json -> java_json

type ejson_uri_runtime_op =
| EJsonRuntimeUriEncode
| EJsonRuntimeUriDecode

val ejson_uri_runtime_op_tostring : ejson_uri_runtime_op -> char list

val log_unary_op_tostring : __ -> char list

val cname0 : nstring

val log_to_java_unary_op : int -> nstring -> nstring -> java_json -> java_json

val ejson_log_runtime_op_tostring : __ -> char list

type math_unary_op =
| Uop_math_float_of_string
| Uop_math_acos
| Uop_math_asin
| Uop_math_atan
| Uop_math_cos
| Uop_math_cosh
| Uop_math_sin
| Uop_math_sinh
| Uop_math_tan
| Uop_math_tanh

val math_unary_op_tostring : math_unary_op -> char list

val math_binary_op_tostring : __ -> char list

val cname1 : nstring

val math_to_java_unary_op :
  int -> nstring -> nstring -> math_unary_op -> java_json -> java_json

val math_to_java_binary_op :
  int -> nstring -> nstring -> java_json -> java_json -> java_json

type ejson_math_runtime_op =
| EJsonRuntimeFloatOfString
| EJsonRuntimeAcos
| EJsonRuntimeAsin
| EJsonRuntimeAtan
| EJsonRuntimeAtan2
| EJsonRuntimeCos
| EJsonRuntimeCosh
| EJsonRuntimeSin
| EJsonRuntimeSinh
| EJsonRuntimeTan
| EJsonRuntimeTanh

val ejson_math_runtime_op_tostring : ejson_math_runtime_op -> char list

type dATE_TIME_FORMAT = Date_time_component.date_time_format

type dATE_TIME_DURATION = Date_time_component.duration

type dATE_TIME_PERIOD = Date_time_component.period

type dATE_TIME = Date_time_component.dateTime

val date_time_format_foreign_data_obligation_3 :
  dATE_TIME_FORMAT -> dATE_TIME_FORMAT

val date_time_format_foreign_data_obligation_1 : dATE_TIME_FORMAT eqDec

val date_time_format_foreign_data_obligation_6 : dATE_TIME_FORMAT toString

val date_time_format_foreign_data : foreign_data

val date_time_duration_foreign_data_obligation_3 :
  dATE_TIME_DURATION -> dATE_TIME_DURATION

val date_time_duration_foreign_data_obligation_1 : dATE_TIME_DURATION eqDec

val date_time_duration_foreign_data_obligation_6 : dATE_TIME_DURATION toString

val date_time_duration_foreign_data : foreign_data

val date_time_period_foreign_data_obligation_3 :
  dATE_TIME_PERIOD -> dATE_TIME_PERIOD

val date_time_period_foreign_data_obligation_1 : dATE_TIME_PERIOD eqDec

val date_time_period_foreign_data_obligation_6 : dATE_TIME_PERIOD toString

val date_time_period_foreign_data : foreign_data

val date_time_foreign_data_obligation_3 : dATE_TIME -> dATE_TIME

val date_time_foreign_data_obligation_1 : dATE_TIME eqDec

val date_time_foreign_data_obligation_6 : dATE_TIME toString

val date_time_foreign_data : foreign_data

type date_time_unary_op =
| Uop_date_time_get_seconds
| Uop_date_time_get_minutes
| Uop_date_time_get_hours
| Uop_date_time_get_days
| Uop_date_time_get_weeks
| Uop_date_time_get_months
| Uop_date_time_get_quarters
| Uop_date_time_get_years
| Uop_date_time_start_of_day
| Uop_date_time_start_of_week
| Uop_date_time_start_of_month
| Uop_date_time_start_of_quarter
| Uop_date_time_start_of_year
| Uop_date_time_end_of_day
| Uop_date_time_end_of_week
| Uop_date_time_end_of_month
| Uop_date_time_end_of_quarter
| Uop_date_time_end_of_year
| Uop_date_time_format_from_string
| Uop_date_time_from_string
| Uop_date_time_max
| Uop_date_time_min
| Uop_date_time_duration_amount
| Uop_date_time_duration_from_string
| Uop_date_time_duration_from_seconds
| Uop_date_time_duration_from_minutes
| Uop_date_time_duration_from_hours
| Uop_date_time_duration_from_days
| Uop_date_time_duration_from_weeks
| Uop_date_time_period_from_string
| Uop_date_time_period_from_days
| Uop_date_time_period_from_weeks
| Uop_date_time_period_from_months
| Uop_date_time_period_from_quarters
| Uop_date_time_period_from_years

type date_time_binary_op =
| Bop_date_time_format
| Bop_date_time_add
| Bop_date_time_subtract
| Bop_date_time_add_period
| Bop_date_time_subtract_period
| Bop_date_time_is_same
| Bop_date_time_is_before
| Bop_date_time_is_after
| Bop_date_time_diff

val date_time_unary_op_tostring : date_time_unary_op -> char list

val date_time_binary_op_tostring : date_time_binary_op -> char list

val cname2 : nstring

val date_time_to_java_unary_op :
  int -> nstring -> nstring -> date_time_unary_op -> java_json -> java_json

val date_time_to_java_binary_op :
  int -> nstring -> nstring -> date_time_binary_op -> java_json -> java_json
  -> java_json

type ejson_date_time_runtime_op =
| EJsonRuntimeDateTimeGetSeconds
| EJsonRuntimeDateTimeGetMinutes
| EJsonRuntimeDateTimeGetHours
| EJsonRuntimeDateTimeGetDays
| EJsonRuntimeDateTimeGetWeeks
| EJsonRuntimeDateTimeGetMonths
| EJsonRuntimeDateTimeGetQuarters
| EJsonRuntimeDateTimeGetYears
| EJsonRuntimeDateTimeStartOfDay
| EJsonRuntimeDateTimeStartOfWeek
| EJsonRuntimeDateTimeStartOfMonth
| EJsonRuntimeDateTimeStartOfQuarter
| EJsonRuntimeDateTimeStartOfYear
| EJsonRuntimeDateTimeEndOfDay
| EJsonRuntimeDateTimeEndOfWeek
| EJsonRuntimeDateTimeEndOfMonth
| EJsonRuntimeDateTimeEndOfQuarter
| EJsonRuntimeDateTimeEndOfYear
| EJsonRuntimeDateTimeFormatFromString
| EJsonRuntimeDateTimeFromString
| EJsonRuntimeDateTimeMax
| EJsonRuntimeDateTimeMin
| EJsonRuntimeDateTimeDurationAmount
| EJsonRuntimeDateTimeDurationFromString
| EJsonRuntimeDateTimePeriodFromString
| EJsonRuntimeDateTimeDurationFromSeconds
| EJsonRuntimeDateTimeDurationFromMinutes
| EJsonRuntimeDateTimeDurationFromHours
| EJsonRuntimeDateTimeDurationFromDays
| EJsonRuntimeDateTimeDurationFromWeeks
| EJsonRuntimeDateTimePeriodFromDays
| EJsonRuntimeDateTimePeriodFromWeeks
| EJsonRuntimeDateTimePeriodFromMonths
| EJsonRuntimeDateTimePeriodFromQuarters
| EJsonRuntimeDateTimePeriodFromYears
| EJsonRuntimeDateTimeFormat
| EJsonRuntimeDateTimeAdd
| EJsonRuntimeDateTimeSubtract
| EJsonRuntimeDateTimeAddPeriod
| EJsonRuntimeDateTimeSubtractPeriod
| EJsonRuntimeDateTimeIsSame
| EJsonRuntimeDateTimeIsBefore
| EJsonRuntimeDateTimeIsAfter
| EJsonRuntimeDateTimeDiff

val ejson_date_time_runtime_op_tostring :
  ejson_date_time_runtime_op -> char list

type enhanced_data =
| EnhanceddateTimeformat of dATE_TIME_FORMAT
| EnhanceddateTime of dATE_TIME
| EnhanceddateTimeduration of dATE_TIME_DURATION
| EnhanceddateTimeperiod of dATE_TIME_PERIOD

val enhanceddateTime_now : dATE_TIME

val enhanced_foreign_data_obligation_3 : enhanced_data -> enhanced_data

val enhanced_foreign_data_obligation_1 : enhanced_data eqDec

val enhanced_foreign_data_obligation_6 : enhanced_data toString

val enhanced_foreign_data : foreign_data

val denhanceddateTimeformat : dATE_TIME_FORMAT -> data

val denhanceddateTime : dATE_TIME -> data

val denhanceddateTimeduration : dATE_TIME_DURATION -> data

val denhanceddateTimeperiod : dATE_TIME_PERIOD -> data

type enhanced_unary_op =
| Enhanced_unary_uri_op of uri_unary_op
| Enhanced_unary_log_op
| Enhanced_unary_math_op of math_unary_op
| Enhanced_unary_date_time_op of date_time_unary_op

val onddateTime : (dATE_TIME -> 'a1) -> data -> 'a1 option

val lift_dateTimeList : data list -> dATE_TIME list option

val onddateTimeList :
  (dATE_TIME list -> dATE_TIME) -> data -> dATE_TIME option

val onddateTimeduration : (dATE_TIME_DURATION -> 'a1) -> data -> 'a1 option

val onddateTimeDurationNat : (int -> 'a1) -> data -> 'a1 option

val onddateTimePeriodNat : (int -> 'a1) -> data -> 'a1 option

val ondstring0 : (char list -> 'a1) -> data -> 'a1 option

val ondstringfloatopt : (char list -> float option) -> data -> data option

val ondstringunit : (char list -> unit) -> data -> data option

val ondstringstring : (char list -> char list) -> data -> data option

val ondfloat0 : (float -> 'a1) -> data -> 'a1 option

val uri_unary_op_interp : uri_unary_op -> data -> data option

val log_unary_op_interp : data -> data option

val math_unary_op_interp : math_unary_op -> data -> data option

val date_time_unary_op_interp : date_time_unary_op -> data -> data option

val enhanced_unary_op_interp :
  brand_relation_t -> enhanced_unary_op -> data -> data option

val enumToString : brands -> data -> char list

val dataToString : data -> char list

val dataToText : data -> char list

type enhanced_binary_op =
| Enhanced_binary_math_op
| Enhanced_binary_date_time_op of date_time_binary_op

val ondfloat2 : (float -> float -> 'a1) -> data -> data -> 'a1 option

val onddateTime2 :
  (dATE_TIME -> dATE_TIME -> 'a1) -> data -> data -> 'a1 option

val rondbooldateTime2 :
  (dATE_TIME -> dATE_TIME -> bool) -> data -> data -> data option

val math_binary_op_interp : data -> data -> data option

val date_time_binary_op_interp :
  date_time_binary_op -> data -> data -> data option

val enhanced_binary_op_interp :
  brand_relation_t -> enhanced_binary_op -> data -> data -> data option

val enhanced_foreign_operators_obligation_1 : enhanced_unary_op eqDec

val enhanced_foreign_operators_obligation_2 : enhanced_unary_op toString

val enhanced_foreign_operators_obligation_4 : enhanced_binary_op eqDec

val enhanced_foreign_operators_obligation_5 : enhanced_binary_op toString

val enhanced_foreign_operators : foreign_operators

val enhanced_foreign_runtime : foreign_runtime

type enhanced_ejson = enhanced_data

val enhanced_foreign_ejson_obligation_3 : enhanced_ejson -> enhanced_ejson

val enhanced_foreign_ejson_obligation_1 : enhanced_ejson eqDec

val enhanced_foreign_ejson_obligation_6 : enhanced_ejson toString

val enhanced_foreign_ejson : foreign_ejson

type enhanced_foreign_ejson_runtime_op =
| Enhanced_ejson_uri of ejson_uri_runtime_op
| Enhanced_ejson_log
| Enhanced_ejson_math of ejson_math_runtime_op
| Enhanced_ejson_date_time of ejson_date_time_runtime_op

val enhanced_foreign_ejson_runtime_op_tostring :
  enhanced_foreign_ejson_runtime_op -> char list

val enhanced_ejson_uri_runtime_op_interp :
  ejson_uri_runtime_op -> ejson list -> ejson option

val onjstringunit : (char list -> unit) -> ejson -> ejson option

val enhanced_ejson_log_runtime_op_interp : ejson list -> ejson option

val enhanced_ejson_math_runtime_op_interp :
  ejson_math_runtime_op -> ejson list -> ejson option

val ejson_dates : ejson list -> dATE_TIME list option

val enhanced_ejson_date_time_runtime_op_interp :
  ejson_date_time_runtime_op -> ejson list -> ejson option

val enhanced_foreign_ejson_runtime_op_interp :
  enhanced_foreign_ejson_runtime_op -> ejson list -> ejson option

val ejsonEnumToString : brands -> ejson -> char list

val ejsonLeftToString : char list -> char list

val ejsonRightToString : char list -> char list

val ejsonArrayToString : char list list -> char list

val ejsonObjectToString : (char list * char list) list -> char list

val ejsonToString : ejson -> char list

val ejsonToText : ejson -> char list

val enhanced_foreign_ejson_runtime_obligation_1 :
  enhanced_foreign_ejson_runtime_op eqDec

val enhanced_foreign_ejson_runtime_obligation_2 :
  enhanced_foreign_ejson_runtime_op toString

val enhanced_foreign_ejson_runtime_obligation_3 :
  enhanced_foreign_ejson_runtime_op -> ejson list -> ejson option

val enhanced_foreign_ejson_runtime_obligation_4 : ejson -> char list

val enhanced_foreign_ejson_runtime_obligation_5 : ejson -> char list

val enhanced_foreign_ejson_runtime : foreign_ejson_runtime

val enhanced_foreign_to_ejson_obligation_1 :
  foreign_ejson_model -> foreign_data_model

val enhanced_foreign_to_ejson_obligation_2 :
  foreign_data_model -> foreign_ejson_model

val enhanced_foreign_to_ejson : foreign_to_ejson

val unary_op_to_ejson : enhanced_unary_op -> enhanced_foreign_ejson_runtime_op

val binary_op_to_ejson :
  enhanced_binary_op -> enhanced_foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime_obligation_1 :
  foreign_operators_unary -> foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime_obligation_3 :
  foreign_operators_binary -> foreign_ejson_runtime_op

val enhanced_foreign_to_ejson_runtime : foreign_to_ejson_runtime0

val enhanced_to_java_data : nstring -> enhanced_data -> java_json

val enhanced_to_java_unary_op :
  int -> nstring -> nstring -> enhanced_unary_op -> java_json -> java_json

val enhanced_to_java_binary_op :
  int -> nstring -> nstring -> enhanced_binary_op -> java_json -> java_json
  -> java_json

val enhanced_foreign_to_java : foreign_to_java

val enhanced_ejson_to_ajavascript_expr : enhanced_ejson -> expr

val enhanced_foreign_ejson_to_ajavascript : foreign_ejson_to_ajavascript

type nnrc0 = nnrc

type nnrcKind =
| NnrcExpr
| NnrcStmt

type nnrc_with_substs = nnrc0 * (var * nnrc0) list

val mk_expr_from_vars : foreign_runtime -> nnrc_with_substs -> nnrc0

val stratify1_aux :
  foreign_runtime -> nnrc0 -> nnrcKind -> var list -> (var * nnrc0) list ->
  nnrc_with_substs

val stratify_aux :
  foreign_runtime -> nnrc0 -> nnrcKind -> var list -> nnrc_with_substs

val stratify : foreign_runtime -> nnrc0 -> nnrc0

type enhanced_type =
| EnhancedTop
| EnhancedBottom
| EnhancedString
| EnhancedDateTimeFormat
| EnhancedDateTime
| EnhancedDateTimeDuration
| EnhancedDateTimePeriod

val enhanced_type_join : enhanced_type -> enhanced_type -> enhanced_type

val enhanced_type_meet : enhanced_type -> enhanced_type -> enhanced_type

val enhanced_type_lattice : enhanced_type lattice

val enhanced_foreign_type_obligation_1 : enhanced_type eqDec

val enhanced_foreign_type_obligation_2 :
  enhanced_type -> enhanced_type -> bool

val enhanced_foreign_type : foreign_type

val enhanced_infer_type : enhanced_data -> enhanced_type option

val enhanced_foreign_data_typing_obligation_4 :
  foreign_data_model -> foreign_type_type

val enhanced_foreign_data_typing : foreign_data_typing

val dateTimeFormat : brand_relation -> rtype

val dateTime : brand_relation -> rtype

val dateTimeDuration : brand_relation -> rtype

val dateTimePeriod : brand_relation -> rtype

val isDateTimeFormat : brand_model -> rtype -> bool

val isDateTime : brand_model -> rtype -> bool

val isDateTimeDuration : brand_model -> rtype -> bool

val isDateTimePeriod : brand_model -> rtype -> bool

val isNat : brand_model -> rtype -> bool

val isString : brand_model -> rtype -> bool

val isFloat : brand_model -> rtype -> bool

val tuncoll0 : brand_model -> rtype -> rtype option

val uri_unary_op_type_infer :
  brand_model -> uri_unary_op -> rtype -> rtype option

val log_unary_op_type_infer : brand_model -> rtype -> rtype option

val math_unary_op_type_infer :
  brand_model -> math_unary_op -> rtype -> rtype option

val date_time_unary_op_type_infer :
  brand_model -> date_time_unary_op -> rtype -> rtype option

val uri_unary_op_type_infer_sub :
  brand_model -> uri_unary_op -> rtype -> (rtype * rtype) option

val log_unary_op_type_infer_sub :
  brand_model -> rtype -> (rtype * rtype) option

val math_unary_op_type_infer_sub :
  brand_model -> math_unary_op -> rtype -> (rtype * rtype) option

val date_time_unary_op_type_infer_sub :
  brand_model -> date_time_unary_op -> rtype -> (rtype * rtype) option

val enhanced_unary_op_typing_infer :
  brand_model -> enhanced_unary_op -> rtype -> rtype option

val enhanced_unary_op_typing_infer_sub :
  brand_model -> enhanced_unary_op -> rtype -> (rtype * rtype) option

val math_binary_op_type_infer : brand_model -> rtype -> rtype -> rtype option

val date_time_binary_op_type_infer :
  brand_model -> date_time_binary_op -> rtype -> rtype -> rtype option

val math_binary_op_type_infer_sub :
  brand_model -> rtype -> rtype -> ((rtype * rtype) * rtype) option

val date_time_binary_op_type_infer_sub :
  brand_model -> date_time_binary_op -> rtype -> rtype ->
  ((rtype * rtype) * rtype) option

val enhanced_binary_op_typing_infer :
  brand_model -> enhanced_binary_op -> rtype -> rtype -> rtype option

val enhanced_binary_op_typing_infer_sub :
  brand_model -> enhanced_binary_op -> rtype -> rtype ->
  ((rtype * rtype) * rtype) option

val enhanced_foreign_operators_typing :
  brand_model -> foreign_operators_typing

val enhanced_foreign_typing : brand_model -> foreign_typing

val enhanced_basic_model : brand_model -> basic_model

module CompEnhanced :
 sig
  module Enhanced :
   sig
    module Model :
     sig
      val basic_model : brand_model -> basic_model

      val foreign_type : foreign_type

      val foreign_typing : brand_model -> foreign_typing
     end

    module Data :
     sig
      val ddate_time : dATE_TIME -> data

      val ddate_time_duration : dATE_TIME_DURATION -> data

      val ddate_time_period : dATE_TIME_PERIOD -> data
     end

    module Ops :
     sig
      module Unary :
       sig
        val date_time_get_seconds : unary_op

        val date_time_get_minutes : unary_op

        val date_time_get_hours : unary_op

        val date_time_get_days : unary_op

        val date_time_get_weeks : unary_op

        val date_time_get_months : unary_op

        val date_time_get_quarters : unary_op

        val date_time_get_years : unary_op

        val date_time_start_of_day : unary_op

        val date_time_start_of_week : unary_op

        val date_time_start_of_month : unary_op

        val date_time_start_of_quarter : unary_op

        val date_time_start_of_year : unary_op

        val date_time_end_of_day : unary_op

        val date_time_end_of_week : unary_op

        val date_time_end_of_month : unary_op

        val date_time_end_of_quarter : unary_op

        val date_time_end_of_year : unary_op

        val date_time_format_from_string : unary_op

        val date_time_from_string : unary_op

        val date_time_min : unary_op

        val date_time_max : unary_op

        val date_time_duration_amount : unary_op

        val date_time_duration_from_string : unary_op

        val date_time_duration_from_seconds : unary_op

        val date_time_duration_from_minutes : unary_op

        val date_time_duration_from_hours : unary_op

        val date_time_duration_from_days : unary_op

        val date_time_duration_from_weeks : unary_op

        val date_time_period_from_string : unary_op

        val date_time_period_from_days : unary_op

        val date_time_period_from_weeks : unary_op

        val date_time_period_from_months : unary_op

        val date_time_period_from_quarters : unary_op

        val date_time_period_from_years : unary_op

        val coq_OpDateTimeGetSeconds : unary_op

        val coq_OpDateTimeGetMinutes : unary_op

        val coq_OpDateTimeGetHours : unary_op

        val coq_OpDateTimeGetDays : unary_op

        val coq_OpDateTimeGetWeeks : unary_op

        val coq_OpDateTimeGetMonths : unary_op

        val coq_OpDateTimeGetQuarters : unary_op

        val coq_OpDateTimeGetYears : unary_op

        val coq_OpDateTimeStartOfDay : unary_op

        val coq_OpDateTimeStartOfWeek : unary_op

        val coq_OpDateTimeStartOfMonth : unary_op

        val coq_OpDateTimeStartOfQuarter : unary_op

        val coq_OpDateTimeStartOfYear : unary_op

        val coq_OpDateTimeEndOfDay : unary_op

        val coq_OpDateTimeEndOfWeek : unary_op

        val coq_OpDateTimeEndOfMonth : unary_op

        val coq_OpDateTimeEndOfQuarter : unary_op

        val coq_OpDateTimeEndOfYear : unary_op

        val coq_OpDateTimeFormatFromString : unary_op

        val coq_OpDateTimeFromString : unary_op

        val coq_OpDateTimeMax : unary_op

        val coq_OpDateTimeMin : unary_op

        val coq_OpDateTimeDurationFromString : unary_op

        val coq_OpDateTimeDurationFromSeconds : unary_op

        val coq_OpDateTimeDurationFromMinutes : unary_op

        val coq_OpDateTimeDurationFromHours : unary_op

        val coq_OpDateTimeDurationFromDays : unary_op

        val coq_OpDateTimeDurationFromWeeks : unary_op

        val coq_OpDateTimePeriodFromString : unary_op

        val coq_OpDateTimePeriodFromDays : unary_op

        val coq_OpDateTimePeriodFromWeeks : unary_op

        val coq_OpDateTimePeriodFromMonths : unary_op

        val coq_OpDateTimePeriodFromQuarters : unary_op

        val coq_OpDateTimePeriodFromYears : unary_op
       end

      module Binary :
       sig
        val date_time_format : binary_op

        val date_time_add : binary_op

        val date_time_subtract : binary_op

        val date_time_add_period : binary_op

        val date_time_subtract_period : binary_op

        val date_time_is_same : binary_op

        val date_time_is_before : binary_op

        val date_time_is_after : binary_op

        val date_time_diff : binary_op

        val coq_OpDateTimeFormat : binary_op

        val coq_OpDateTimeAdd : binary_op

        val coq_OpDateTimeSubtract : binary_op

        val coq_OpDateTimeIsBefore : binary_op

        val coq_OpDateTimeIsAfter : binary_op

        val coq_OpDateTimeDiff : binary_op
       end
     end
   end
 end

module type QBackendModel =
 sig
  val ergo_foreign_data : foreign_data

  val ergo_foreign_type : foreign_type
 end

module QType :
 functor (Coq_ergomodel:QBackendModel) ->
 sig
  val empty_brand_model : unit -> brand_model

  type record_kind = Coq__2.record_kind

  val open_kind : record_kind

  val closed_kind : record_kind

  type qtype_struct = rtype_UU2080_

  type qtype = rtype

  type t = qtype

  val tbottom : brand_relation -> qtype

  val ttop : brand_relation -> qtype

  val tunit : brand_relation -> qtype

  val tfloat : brand_relation -> qtype

  val tnat : brand_relation -> qtype

  val tbool : brand_relation -> qtype

  val tstring : brand_relation -> qtype

  val tdateTimeFormat : brand_relation -> qtype

  val tdateTime : brand_relation -> qtype

  val tduration : brand_relation -> qtype

  val tperiod : brand_relation -> qtype

  val tcoll : brand_relation -> qtype -> qtype

  val trec :
    brand_relation -> record_kind -> (char list * qtype) list -> qtype

  val teither : brand_relation -> qtype -> qtype -> qtype

  val tarrow : brand_relation -> qtype -> qtype -> qtype

  val tbrand : brand_relation -> char list list -> qtype

  val toption : brand_relation -> qtype -> qtype

  val qcert_type_meet : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_join : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_subtype_dec : brand_model -> qtype -> qtype -> bool

  val untcoll : brand_model -> qtype -> qtype option

  val unteither : brand_model -> qtype -> (qtype * qtype) option

  val untrec :
    brand_model -> qtype -> (record_kind * (char list * qtype) list) option

  val qcert_type_infer_data : brand_model -> data -> qtype option

  val qcert_type_infer_binary_op :
    brand_model -> binary_op -> qtype -> qtype -> ((qtype * qtype) * qtype)
    option

  val qcert_type_infer_unary_op :
    brand_model -> unary_op -> qtype -> (qtype * qtype) option

  val unpack_qcert_type : brand_relation -> qtype -> qtype_struct

  type tbrand_relation = brand_relation

  val tempty_brand_relation : tbrand_relation

  val mk_tbrand_relation :
    (char list * char list) list -> tbrand_relation qresult

  type tbrand_context_decls = brand_context_decls

  type tbrand_context = brand_context

  val mk_tbrand_context :
    brand_relation -> tbrand_context_decls -> tbrand_context

  type tbrand_model = brand_model

  val mk_tbrand_model :
    brand_relation -> tbrand_context_decls -> tbrand_model qresult

  val tempty_brand_model : tbrand_model

  val qcert_type_unpack : brand_relation -> qtype -> qtype_struct

  val qcert_type_closed_from_open : brand_model -> qtype -> qtype

  val infer_brand_strict :
    brand_model -> brands -> qtype -> (rtype * qtype) option

  val recminus :
    brand_relation -> (char list * rtype) list -> char list list ->
    (char list * rtype) list

  val diff_record_types :
    brand_model -> brands -> qtype -> (char list list * char list list) option

  val rec_fields_that_are_not_subtype :
    brand_model -> (char list * qtype) list -> (char list * qtype) list ->
    ((char list * qtype) * qtype) list

  val fields_that_are_not_subtype :
    brand_model -> brands -> qtype -> ((char list * qtype) * qtype) list
 end

module QData :
 functor (Coq_ergomodel:QBackendModel) ->
 sig
  type json = Coq__3.json

  type data = Coq__4.data

  type t = data

  val jnull : json

  val jnumber : float -> json

  val jbool : bool -> json

  val jstring : char list -> json

  val jarray : Coq__3.json list -> json

  val jobject : (char list * Coq__3.json) list -> json

  val dunit : data

  val dnat : int -> data

  val dfloat : float -> data

  val dbool : bool -> data

  val dstring : char list -> data

  val dcoll : Coq__4.data list -> data

  val drec : (char list * Coq__4.data) list -> data

  val dleft : data -> data

  val dright : data -> data

  val dbrand : brands -> data -> data

  val dsome : data -> data

  val dnone : data

  val dsuccess : data -> data

  val derror : data -> data
 end

module QOps :
 functor (Coq_ergomodel:QBackendModel) ->
 sig
  module ErgoData :
   sig
    type json = Coq__3.json

    type data = Coq__4.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : Coq__3.json list -> json

    val jobject : (char list * Coq__3.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Coq__4.data list -> data

    val drec : (char list * Coq__4.data) list -> data

    val dleft : data -> data

    val dright : data -> data

    val dbrand : brands -> data -> data

    val dsome : data -> data

    val dnone : data

    val dsuccess : data -> data

    val derror : data -> data
   end

  module Unary :
   sig
    type op = unary_op

    type t = op

    module Double :
     sig
      val opuminus : op

      val opabs : op

      val oplog2 : op

      val opsqrt : op

      val opsum : op

      val opnummin : op

      val opnummax : op

      val opnummean : op
     end

    val opidentity : op

    val opneg : op

    val oprec : char list -> op

    val opdot : char list -> op

    val oprecremove : char list -> op

    val oprecproject : char list list -> op

    val opbag : op

    val opsingleton : op

    val opflatten : op

    val opdistinct : op

    val opcount : op

    val optostring : op

    val opsubstring : int -> int option -> op

    val oplike : char list -> op

    val opleft : op

    val opright : op

    val opbrand : brands -> op

    val opunbrand : op

    val opcast : brands -> op

    val eval :
      brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option
   end

  module Binary :
   sig
    type op = binary_op

    type t = op

    module Double :
     sig
      val opplus : op

      val opminus : op

      val opmult : op

      val opmin : op

      val opmax : op

      val opdiv : op

      val oppow : op

      val oplt : op

      val ople : op

      val opgt : op

      val opge : op
     end

    module Integer :
     sig
      val opplusi : op

      val opminusi : op

      val opmulti : op

      val opdivi : op

      val oplti : op

      val oplei : op
     end

    module DateTime :
     sig
      val opdateadd : op

      val opdatesubtract : op

      val opdateisbefore : op

      val opdateisafter : op

      val opdatediff : op
     end

    val opequal : op

    val oprecconcat : op

    val oprecmerge : op

    val opand : op

    val opor : op

    val opbagunion : op

    val opbagdiff : op

    val opbagmin : op

    val opbagmax : op

    val opnth : op

    val opcontains : op

    val opstringconcat : op

    val opstringjoin : op

    val eval :
      brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
      ErgoData.data option
   end
 end

val array_push : expr -> expr -> expr

val array_get : expr -> expr -> expr

val object_hasOwnProperty : expr -> expr -> expr

val call_js_function : char list -> expr list -> expr

val call_runtime : char list -> expr list -> expr

val nnrs_imp_expr_free_vars : foreign_runtime -> nnrs_imp_expr -> var list

val nnrs_imp_stmt_free_vars : foreign_runtime -> nnrs_imp_stmt -> var list

val nnrs_imp_stmt_bound_vars : foreign_runtime -> nnrs_imp_stmt -> var list

type var1 = char list

type ('constant, 'op, 'runtime) imp_expr =
| ImpExprError of char list
| ImpExprVar of var1
| ImpExprConst of 'constant
| ImpExprOp of 'op * ('constant, 'op, 'runtime) imp_expr list
| ImpExprRuntimeCall of 'runtime * ('constant, 'op, 'runtime) imp_expr list

type ('constant, 'op, 'runtime) imp_stmt =
| ImpStmtBlock of (var1 * ('constant, 'op, 'runtime) imp_expr option) list
   * ('constant, 'op, 'runtime) imp_stmt list
| ImpStmtAssign of var1 * ('constant, 'op, 'runtime) imp_expr
| ImpStmtFor of var1 * ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_stmt
| ImpStmtForRange of var1 * ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_expr * ('constant, 'op, 'runtime) imp_stmt
| ImpStmtIf of ('constant, 'op, 'runtime) imp_expr
   * ('constant, 'op, 'runtime) imp_stmt * ('constant, 'op, 'runtime) imp_stmt

type ('constant, 'op, 'runtime) imp_function =
| ImpFun of var1 * ('constant, 'op, 'runtime) imp_stmt * var1

type ('constant, 'op, 'runtime) imp =
  (char list * ('constant, 'op, 'runtime) imp_function) list
  (* singleton inductive, whose constructor was ImpLib *)

type imp_data_constant = data

type imp_data_op =
| DataOpUnary of unary_op
| DataOpBinary of binary_op

type imp_data_runtime_op =
| DataRuntimeGroupby of char list * char list list
| DataRuntimeEither
| DataRuntimeToLeft
| DataRuntimeToRight

type imp_data_expr =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_expr

type imp_data_stmt =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_stmt

type imp_data_function =
  (imp_data_constant, imp_data_op, imp_data_runtime_op) imp_function

type imp_data = (imp_data_constant, imp_data_op, imp_data_runtime_op) imp

val nnrs_imp_expr_to_imp_data :
  foreign_runtime -> char list -> nnrs_imp_expr -> imp_data_expr

val nnrs_imp_stmt_to_imp_data :
  foreign_runtime -> char list -> nnrs_imp_stmt -> imp_data_stmt

val nnrs_imp_to_imp_data_function :
  foreign_runtime -> nnrs_imp -> (imp_data_constant, imp_data_op,
  imp_data_runtime_op) imp_function

val nnrs_imp_to_imp_data_top :
  foreign_runtime -> char list -> nnrs_imp -> (imp_data_constant,
  imp_data_op, imp_data_runtime_op) imp

type imp_ejson_model = ejson

type imp_ejson_op = ejson_op

type imp_ejson_runtime_op = ejson_runtime_op

type imp_ejson_expr =
  (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_expr

type imp_ejson_stmt =
  (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_stmt

module Coq__5 : sig
 type imp_ejson_function =
   (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_function
end
include module type of struct include Coq__5 end

type imp_ejson = (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp

val mk_imp_ejson_expr_error :
  foreign_ejson -> foreign_ejson_runtime -> char list -> imp_ejson_expr

val mk_imp_ejson_op :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_op -> (imp_ejson_model,
  imp_ejson_op, imp_ejson_runtime_op) imp_expr list -> imp_ejson_expr

val mk_imp_ejson_runtime_call :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_runtime_op ->
  (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_expr list ->
  imp_ejson_expr

val mk_string :
  foreign_ejson -> foreign_ejson_runtime -> char list -> imp_ejson_expr

val mk_string_array :
  foreign_ejson -> foreign_ejson_runtime -> char list list -> imp_ejson_expr

val mk_bag :
  foreign_ejson -> foreign_ejson_runtime -> (imp_ejson_model, imp_ejson_op,
  imp_ejson_runtime_op) imp_expr list -> imp_ejson_expr

val mk_left :
  foreign_ejson -> foreign_ejson_runtime -> (imp_ejson_model, imp_ejson_op,
  imp_ejson_runtime_op) imp_expr -> imp_ejson_expr

val mk_right :
  foreign_ejson -> foreign_ejson_runtime -> (imp_ejson_model, imp_ejson_op,
  imp_ejson_runtime_op) imp_expr -> imp_ejson_expr

val sortCriterias_to_ejson_expr :
  foreign_ejson -> foreign_ejson_runtime -> (char list * sortDesc) list ->
  imp_ejson_expr

val brands_to_ejson_expr :
  foreign_ejson -> foreign_ejson_runtime -> char list list -> imp_ejson_expr

val mk_either_expr :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_expr list ->
  imp_ejson_expr

val mk_to_left_expr :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_expr list ->
  imp_ejson_expr

val mk_to_right_expr :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_expr list ->
  imp_ejson_expr

val imp_data_unary_op_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  unary_op -> imp_ejson_expr list -> imp_ejson_expr

val imp_data_binary_op_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> binary_op ->
  (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_expr list ->
  imp_ejson_expr

val imp_data_op_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  imp_data_op -> imp_ejson_expr list -> imp_ejson_expr

val imp_data_runtime_call_to_imp_ejson :
  foreign_ejson -> foreign_ejson_runtime -> imp_data_runtime_op ->
  imp_ejson_expr list -> imp_ejson_expr

val imp_data_expr_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  imp_data_expr -> imp_ejson_expr

val imp_data_stmt_to_imp_ejson_combined :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  char list list -> imp_data_stmt -> imp_ejson_stmt

val imp_data_function_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  imp_data_function -> imp_ejson_function

val imp_data_to_imp_ejson :
  foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_ejson_runtime -> foreign_to_ejson_runtime0 -> brand_relation_t ->
  imp_data -> imp_ejson

val scope : stat list -> stat

val prog_to_string : prog -> char list

val box_nat : expr -> expr

val unbox_nat : expr -> expr

val mk_expr_error : expr

val mk_unary_expr : (expr -> expr) -> expr list -> expr

val mk_unary_op : unary_op0 -> expr list -> expr

val mk_binary_expr : (expr -> expr -> expr) -> expr list -> expr

val mk_binary_op : binary_op0 -> expr list -> expr

val mk_object : char list list -> expr list -> expr

val mk_runtime_call :
  foreign_ejson -> foreign_ejson_runtime -> imp_ejson_runtime_op -> expr list
  -> expr

val imp_ejson_op_to_js_ast : imp_ejson_op -> expr list -> expr

val ejson_to_js_ast :
  foreign_ejson -> foreign_ejson_to_ajavascript -> ejson -> expr

val imp_ejson_expr_to_js_ast :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  imp_ejson_expr -> expr

val decl_to_js_ast :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  (var1 * (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_expr
  option) -> var1 * expr option

val imp_ejson_stmt_to_js_ast :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  imp_ejson_stmt -> stat

val imp_ejson_function_to_js_ast :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op) imp_function ->
  char list list * funcbody

val imp_ejson_function_to_funcelement :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  char list -> (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op)
  imp_function -> element

val imp_ejson_function_to_funcdecl :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  char list -> (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op)
  imp_function -> funcdecl

val imp_ejson_function_to_topdecl :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  char list -> (imp_ejson_model, imp_ejson_op, imp_ejson_runtime_op)
  imp_function -> topdecl

val imp_ejson_to_function :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  imp_ejson -> topdecl list

val imp_ejson_to_method :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  imp_ejson -> funcdecl list

val imp_ejson_table_to_topdecls :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  char list -> imp_ejson list -> topdecl list

val imp_ejson_table_to_class :
  foreign_ejson -> foreign_ejson_to_ajavascript -> foreign_ejson_runtime ->
  char list -> imp_ejson -> topdecl

type nnrs_expr =
| NNRSGetConstant of var
| NNRSVar of var
| NNRSConst of data
| NNRSBinop of binary_op * nnrs_expr * nnrs_expr
| NNRSUnop of unary_op * nnrs_expr
| NNRSGroupBy of char list * char list list * nnrs_expr

type nnrs_stmt =
| NNRSSeq of nnrs_stmt * nnrs_stmt
| NNRSLet of var * nnrs_expr * nnrs_stmt
| NNRSLetMut of var * nnrs_stmt * nnrs_stmt
| NNRSLetMutColl of var * nnrs_stmt * nnrs_stmt
| NNRSAssign of var * nnrs_expr
| NNRSPush of var * nnrs_expr
| NNRSFor of var * nnrs_expr * nnrs_stmt
| NNRSIf of nnrs_expr * nnrs_stmt * nnrs_stmt
| NNRSEither of nnrs_expr * var * nnrs_stmt * var * nnrs_stmt

type nnrs = nnrs_stmt * var

val nnrs_expr_free_vars : foreign_runtime -> nnrs_expr -> var list

val nnrs_stmt_free_env_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_free_mcenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_free_mdenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_env_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_mcenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_bound_mdenv_vars : foreign_runtime -> nnrs_stmt -> var list

val nnrs_stmt_rename_mc :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt

val nnrs_stmt_rename_md :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt

val nnrs_expr_rename_env :
  foreign_runtime -> nnrs_expr -> var -> var -> nnrs_expr

val nnrs_stmt_rename_env :
  foreign_runtime -> nnrs_stmt -> var -> var -> nnrs_stmt

val nnrs_stmt_uncross_shadow_under :
  foreign_runtime -> char list -> nnrs_stmt -> var list -> var list -> var
  list -> nnrs_stmt

val nnrs_uncross_shadow : foreign_runtime -> char list -> nnrs -> nnrs

type javascript = nstring

type nnrc1 = nnrc0

type nnrs0 = nnrs

type nnrs_imp0 = nnrs_imp

type imp_data0 = imp_data

type imp_ejson0 = imp_ejson

type js_ast0 = js_ast

type javascript0 = javascript

type java0 = java

val nnrc_expr_to_nnrs_expr : foreign_runtime -> nnrc0 -> nnrs_expr option

val nnrc_expr_to_nnrs_expr_stratified_some :
  foreign_runtime -> nnrc0 -> nnrs_expr

type terminator =
| Term_assign of var
| Term_push of var

val terminate : foreign_runtime -> terminator -> nnrs_expr -> nnrs_stmt

val nnrc_stmt_to_nnrs_stmt_aux :
  foreign_runtime -> var list -> terminator -> nnrc0 -> nnrs_stmt option

val nnrc_stmt_to_nnrs :
  foreign_runtime -> var list -> nnrc0 -> (nnrs_stmt * var) option

val nnrc_stmt_to_nnrs_stmt_aux_stratified_some :
  foreign_runtime -> var list -> terminator -> nnrc0 -> nnrs_stmt

val nnrc_stmt_to_nnrs_stmt_stratified_some :
  foreign_runtime -> var list -> nnrc0 -> (nnrs_stmt * var)

val stratified_nnrc_stmt_to_nnrs :
  foreign_runtime -> var list -> nnrc0 -> nnrs

val nnrc_to_nnrs_top : foreign_runtime -> var list -> nnrc0 -> nnrs

val nnrs_expr_to_nnrs_imp_expr : foreign_runtime -> nnrs_expr -> nnrs_imp_expr

val nnrs_stmt_to_nnrs_imp_stmt : foreign_runtime -> nnrs_stmt -> nnrs_imp_stmt

val nnrs_to_nnrs_imp : foreign_runtime -> nnrs -> nnrs_imp

val nnrs_to_nnrs_imp_top : foreign_runtime -> char list -> nnrs -> nnrs_imp

val eol : nstring

val quotel : nstring

val indent0 : int -> nstring

val comma_list_string : char list list -> nstring

val comma_list : nstring list -> nstring

val js_quote_char : char -> nstring

val js_quote_string : char list -> nstring

val js_quote_number : number -> nstring

val nstring_of_literal : literal -> nstring

val nstring_of_propname : propname -> nstring

val nstring_of_expr : expr -> int -> nstring

val nstring_of_stat : stat -> int -> nstring

val nstring_of_element : element -> int -> nstring

val nstring_of_prog : prog -> int -> nstring

val nstring_of_funcbody : funcbody -> int -> nstring

val nstring_of_method : funcdecl -> int -> nstring

val nstring_of_decl : topdecl -> nstring

val js_ast_to_js_top : js_ast -> javascript

val unshadow_java : foreign_runtime -> var list -> nnrc0 -> nnrc0

val mk_java_json_brands : nstring -> brands -> java_json

val mk_java_json_data :
  foreign_runtime -> foreign_to_java -> nstring -> data -> java_json

val uarithToJavaMethod : nat_arith_unary_op -> char list

val float_uarithToJavaMethod : float_arith_unary_op -> char list

val nat_barithToJavaMethod : nat_arith_binary_op -> char list

val float_barithToJavaMethod : float_arith_binary_op -> char list

val float_bcompareToJavaMethod : float_compare_binary_op -> char list

val like_clause_to_java : like_clause -> nstring

val nnrcToJava :
  foreign_runtime -> foreign_to_java -> nnrc0 -> int -> int -> nstring ->
  nstring -> (char list * nstring) list -> (nstring * java_json) * int

val nnrcToJavaunshadow :
  foreign_runtime -> foreign_to_java -> nnrc0 -> int -> int -> nstring ->
  nstring -> var list -> (char list * nstring) list ->
  (nstring * java_json) * int

val makeJavaParams : (char list * nstring) list -> nstring

val closeFreeVars0 :
  foreign_runtime -> char list -> nnrc0 -> (char list * nstring) list -> nnrc0

val nnrcToJavaFun :
  foreign_runtime -> foreign_to_java -> int -> char list -> nnrc0 -> nstring
  -> nstring -> (char list * nstring) list -> nstring -> nstring

val nnrc_to_nnrs : foreign_runtime -> var0 list -> nnrc1 -> nnrs0

val nnrs_to_nnrs_imp0 : foreign_runtime -> nnrs0 -> nnrs_imp0

val nnrs_imp_to_imp_data :
  foreign_runtime -> char list -> nnrs_imp0 -> imp_data0

val imp_data_to_imp_ejson0 :
  foreign_type -> foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_to_ejson_runtime0 -> brand_model -> imp_data0 -> imp_ejson0

val js_ast_to_javascript : js_ast0 -> javascript0

val h : foreign_type -> brand_model -> (char list * char list) list

val nnrc_expr_to_imp_ejson_function :
  foreign_type -> foreign_runtime -> foreign_ejson -> foreign_to_ejson ->
  foreign_to_ejson_runtime0 -> brand_model -> char list list -> nnrc1 ->
  imp_ejson_function

module QCodeGen :
 functor (Coq_ergomodel:QBackendModel) ->
 sig
  type nnrc_expr = nnrc0

  val nnrc_optim : nnrc_expr -> nnrc_expr

  val nnrc_expr_let : var -> nnrc -> nnrc -> nnrc

  val eindent : int -> nstring

  val equotel_double : nstring

  val eeol_newline : nstring

  val javascript_identifier_sanitizer : char list -> char list

  type imp_ejson_function = Coq__5.imp_ejson_function

  type imp_ejson_lib = imp_ejson

  val nnrc_expr_to_imp_ejson_function :
    brand_model -> char list list -> nnrc1 -> Coq__5.imp_ejson_function

  val imp_function_to_javascript_ast :
    brand_model -> char list -> imp_ejson_function -> js_ast0

  val imp_function_table_to_javascript_ast :
    brand_model -> char list -> imp_ejson_lib -> js_ast0

  type ejavascript = javascript0

  val nnrc_expr_to_imp_ejson :
    brand_model -> char list list -> (char list * nnrc1) -> imp_ejson0

  val nnrc_expr_to_javascript_function :
    brand_model -> char list list -> (char list * nnrc1) -> js_ast0

  val nnrc_expr_to_javascript_function_table :
    brand_model -> char list list -> char list -> (char list * nnrc_expr)
    list -> js_ast0

  val js_ast_to_javascript : js_ast0 -> javascript0

  val javascript_of_inheritance : (char list * char list) list -> js_ast0

  type java = java0

  val java_identifier_sanitizer : char list -> char list

  val nnrc_expr_to_java :
    nnrc0 -> int -> int -> nstring -> nstring -> (char list * nstring) list
    -> (nstring * java_json) * int

  val nnrc_expr_java_unshadow :
    nnrc0 -> int -> int -> nstring -> nstring -> var list ->
    (char list * nstring) list -> (nstring * java_json) * int

  val nnrc_expr_to_java_method :
    char list -> nnrc_expr -> int -> nstring -> nstring ->
    (char list * nstring) list -> nstring -> nstring

  type java_data = java_json

  val mk_java_data : nstring -> java_json

  val from_java_data : java_data -> nstring
 end

module QcertBackend :
 sig
  val ergo_foreign_data : foreign_data

  val ergo_foreign_type : foreign_type

  module Enhanced :
   sig
    module Model :
     sig
      val basic_model : brand_model -> basic_model

      val foreign_type : foreign_type

      val foreign_typing : brand_model -> foreign_typing
     end

    module Data :
     sig
      val ddate_time : dATE_TIME -> data

      val ddate_time_duration : dATE_TIME_DURATION -> data

      val ddate_time_period : dATE_TIME_PERIOD -> data
     end

    module Ops :
     sig
      module Unary :
       sig
        val date_time_get_seconds : unary_op

        val date_time_get_minutes : unary_op

        val date_time_get_hours : unary_op

        val date_time_get_days : unary_op

        val date_time_get_weeks : unary_op

        val date_time_get_months : unary_op

        val date_time_get_quarters : unary_op

        val date_time_get_years : unary_op

        val date_time_start_of_day : unary_op

        val date_time_start_of_week : unary_op

        val date_time_start_of_month : unary_op

        val date_time_start_of_quarter : unary_op

        val date_time_start_of_year : unary_op

        val date_time_end_of_day : unary_op

        val date_time_end_of_week : unary_op

        val date_time_end_of_month : unary_op

        val date_time_end_of_quarter : unary_op

        val date_time_end_of_year : unary_op

        val date_time_format_from_string : unary_op

        val date_time_from_string : unary_op

        val date_time_min : unary_op

        val date_time_max : unary_op

        val date_time_duration_amount : unary_op

        val date_time_duration_from_string : unary_op

        val date_time_duration_from_seconds : unary_op

        val date_time_duration_from_minutes : unary_op

        val date_time_duration_from_hours : unary_op

        val date_time_duration_from_days : unary_op

        val date_time_duration_from_weeks : unary_op

        val date_time_period_from_string : unary_op

        val date_time_period_from_days : unary_op

        val date_time_period_from_weeks : unary_op

        val date_time_period_from_months : unary_op

        val date_time_period_from_quarters : unary_op

        val date_time_period_from_years : unary_op

        val coq_OpDateTimeGetSeconds : unary_op

        val coq_OpDateTimeGetMinutes : unary_op

        val coq_OpDateTimeGetHours : unary_op

        val coq_OpDateTimeGetDays : unary_op

        val coq_OpDateTimeGetWeeks : unary_op

        val coq_OpDateTimeGetMonths : unary_op

        val coq_OpDateTimeGetQuarters : unary_op

        val coq_OpDateTimeGetYears : unary_op

        val coq_OpDateTimeStartOfDay : unary_op

        val coq_OpDateTimeStartOfWeek : unary_op

        val coq_OpDateTimeStartOfMonth : unary_op

        val coq_OpDateTimeStartOfQuarter : unary_op

        val coq_OpDateTimeStartOfYear : unary_op

        val coq_OpDateTimeEndOfDay : unary_op

        val coq_OpDateTimeEndOfWeek : unary_op

        val coq_OpDateTimeEndOfMonth : unary_op

        val coq_OpDateTimeEndOfQuarter : unary_op

        val coq_OpDateTimeEndOfYear : unary_op

        val coq_OpDateTimeFormatFromString : unary_op

        val coq_OpDateTimeFromString : unary_op

        val coq_OpDateTimeMax : unary_op

        val coq_OpDateTimeMin : unary_op

        val coq_OpDateTimeDurationFromString : unary_op

        val coq_OpDateTimeDurationFromSeconds : unary_op

        val coq_OpDateTimeDurationFromMinutes : unary_op

        val coq_OpDateTimeDurationFromHours : unary_op

        val coq_OpDateTimeDurationFromDays : unary_op

        val coq_OpDateTimeDurationFromWeeks : unary_op

        val coq_OpDateTimePeriodFromString : unary_op

        val coq_OpDateTimePeriodFromDays : unary_op

        val coq_OpDateTimePeriodFromWeeks : unary_op

        val coq_OpDateTimePeriodFromMonths : unary_op

        val coq_OpDateTimePeriodFromQuarters : unary_op

        val coq_OpDateTimePeriodFromYears : unary_op
       end

      module Binary :
       sig
        val date_time_format : binary_op

        val date_time_add : binary_op

        val date_time_subtract : binary_op

        val date_time_add_period : binary_op

        val date_time_subtract_period : binary_op

        val date_time_is_same : binary_op

        val date_time_is_before : binary_op

        val date_time_is_after : binary_op

        val date_time_diff : binary_op

        val coq_OpDateTimeFormat : binary_op

        val coq_OpDateTimeAdd : binary_op

        val coq_OpDateTimeSubtract : binary_op

        val coq_OpDateTimeIsBefore : binary_op

        val coq_OpDateTimeIsAfter : binary_op

        val coq_OpDateTimeDiff : binary_op
       end
     end
   end
 end

module QcertData :
 sig
  type json = Coq__3.json

  type data = Coq__4.data

  type t = data

  val jnull : json

  val jnumber : float -> json

  val jbool : bool -> json

  val jstring : char list -> json

  val jarray : Coq__3.json list -> json

  val jobject : (char list * Coq__3.json) list -> json

  val dunit : data

  val dnat : int -> data

  val dfloat : float -> data

  val dbool : bool -> data

  val dstring : char list -> data

  val dcoll : Coq__4.data list -> data

  val drec : (char list * Coq__4.data) list -> data

  val dleft : data -> data

  val dright : data -> data

  val dbrand : brands -> data -> data

  val dsome : data -> data

  val dnone : data

  val dsuccess : data -> data

  val derror : data -> data
 end

module QcertOps :
 sig
  module ErgoData :
   sig
    type json = Coq__3.json

    type data = Coq__4.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : Coq__3.json list -> json

    val jobject : (char list * Coq__3.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Coq__4.data list -> data

    val drec : (char list * Coq__4.data) list -> data

    val dleft : data -> data

    val dright : data -> data

    val dbrand : brands -> data -> data

    val dsome : data -> data

    val dnone : data

    val dsuccess : data -> data

    val derror : data -> data
   end

  module Unary :
   sig
    type op = unary_op

    type t = op

    module Double :
     sig
      val opuminus : op

      val opabs : op

      val oplog2 : op

      val opsqrt : op

      val opsum : op

      val opnummin : op

      val opnummax : op

      val opnummean : op
     end

    val opidentity : op

    val opneg : op

    val oprec : char list -> op

    val opdot : char list -> op

    val oprecremove : char list -> op

    val oprecproject : char list list -> op

    val opbag : op

    val opsingleton : op

    val opflatten : op

    val opdistinct : op

    val opcount : op

    val optostring : op

    val opsubstring : int -> int option -> op

    val oplike : char list -> op

    val opleft : op

    val opright : op

    val opbrand : brands -> op

    val opunbrand : op

    val opcast : brands -> op

    val eval :
      brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option
   end

  module Binary :
   sig
    type op = binary_op

    type t = op

    module Double :
     sig
      val opplus : op

      val opminus : op

      val opmult : op

      val opmin : op

      val opmax : op

      val opdiv : op

      val oppow : op

      val oplt : op

      val ople : op

      val opgt : op

      val opge : op
     end

    module Integer :
     sig
      val opplusi : op

      val opminusi : op

      val opmulti : op

      val opdivi : op

      val oplti : op

      val oplei : op
     end

    module DateTime :
     sig
      val opdateadd : op

      val opdatesubtract : op

      val opdateisbefore : op

      val opdateisafter : op

      val opdatediff : op
     end

    val opequal : op

    val oprecconcat : op

    val oprecmerge : op

    val opand : op

    val opor : op

    val opbagunion : op

    val opbagdiff : op

    val opbagmin : op

    val opbagmax : op

    val opnth : op

    val opcontains : op

    val opstringconcat : op

    val opstringjoin : op

    val eval :
      brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
      ErgoData.data option
   end
 end

module QcertCodeGen :
 sig
  type nnrc_expr = nnrc0

  val nnrc_optim : nnrc_expr -> nnrc_expr

  val nnrc_expr_let : var -> nnrc -> nnrc -> nnrc

  val eindent : int -> nstring

  val equotel_double : nstring

  val eeol_newline : nstring

  val javascript_identifier_sanitizer : char list -> char list

  type imp_ejson_function = Coq__5.imp_ejson_function

  type imp_ejson_lib = imp_ejson

  val nnrc_expr_to_imp_ejson_function :
    brand_model -> char list list -> nnrc1 -> Coq__5.imp_ejson_function

  val imp_function_to_javascript_ast :
    brand_model -> char list -> imp_ejson_function -> js_ast0

  val imp_function_table_to_javascript_ast :
    brand_model -> char list -> imp_ejson_lib -> js_ast0

  type ejavascript = javascript0

  val nnrc_expr_to_imp_ejson :
    brand_model -> char list list -> (char list * nnrc1) -> imp_ejson0

  val nnrc_expr_to_javascript_function :
    brand_model -> char list list -> (char list * nnrc1) -> js_ast0

  val nnrc_expr_to_javascript_function_table :
    brand_model -> char list list -> char list -> (char list * nnrc_expr)
    list -> js_ast0

  val js_ast_to_javascript : js_ast0 -> javascript0

  val javascript_of_inheritance : (char list * char list) list -> js_ast0

  type java = java0

  val java_identifier_sanitizer : char list -> char list

  val nnrc_expr_to_java :
    nnrc0 -> int -> int -> nstring -> nstring -> (char list * nstring) list
    -> (nstring * java_json) * int

  val nnrc_expr_java_unshadow :
    nnrc0 -> int -> int -> nstring -> nstring -> var list ->
    (char list * nstring) list -> (nstring * java_json) * int

  val nnrc_expr_to_java_method :
    char list -> nnrc_expr -> int -> nstring -> nstring ->
    (char list * nstring) list -> nstring -> nstring

  type java_data = java_json

  val mk_java_data : nstring -> java_json

  val from_java_data : java_data -> nstring
 end

module QcertType :
 sig
  val empty_brand_model : unit -> brand_model

  type record_kind = Coq__2.record_kind

  val open_kind : record_kind

  val closed_kind : record_kind

  type qtype_struct = rtype_UU2080_

  type qtype = rtype

  type t = qtype

  val tbottom : brand_relation -> qtype

  val ttop : brand_relation -> qtype

  val tunit : brand_relation -> qtype

  val tfloat : brand_relation -> qtype

  val tnat : brand_relation -> qtype

  val tbool : brand_relation -> qtype

  val tstring : brand_relation -> qtype

  val tdateTimeFormat : brand_relation -> qtype

  val tdateTime : brand_relation -> qtype

  val tduration : brand_relation -> qtype

  val tperiod : brand_relation -> qtype

  val tcoll : brand_relation -> qtype -> qtype

  val trec :
    brand_relation -> record_kind -> (char list * qtype) list -> qtype

  val teither : brand_relation -> qtype -> qtype -> qtype

  val tarrow : brand_relation -> qtype -> qtype -> qtype

  val tbrand : brand_relation -> char list list -> qtype

  val toption : brand_relation -> qtype -> qtype

  val qcert_type_meet : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_join : brand_relation -> qtype -> qtype -> qtype

  val qcert_type_subtype_dec : brand_model -> qtype -> qtype -> bool

  val untcoll : brand_model -> qtype -> qtype option

  val unteither : brand_model -> qtype -> (qtype * qtype) option

  val untrec :
    brand_model -> qtype -> (record_kind * (char list * qtype) list) option

  val qcert_type_infer_data : brand_model -> data -> qtype option

  val qcert_type_infer_binary_op :
    brand_model -> binary_op -> qtype -> qtype -> ((qtype * qtype) * qtype)
    option

  val qcert_type_infer_unary_op :
    brand_model -> unary_op -> qtype -> (qtype * qtype) option

  val unpack_qcert_type : brand_relation -> qtype -> qtype_struct

  type tbrand_relation = brand_relation

  val tempty_brand_relation : tbrand_relation

  val mk_tbrand_relation :
    (char list * char list) list -> tbrand_relation qresult

  type tbrand_context_decls = brand_context_decls

  type tbrand_context = brand_context

  val mk_tbrand_context :
    brand_relation -> tbrand_context_decls -> tbrand_context

  type tbrand_model = brand_model

  val mk_tbrand_model :
    brand_relation -> tbrand_context_decls -> tbrand_model qresult

  val tempty_brand_model : tbrand_model

  val qcert_type_unpack : brand_relation -> qtype -> qtype_struct

  val qcert_type_closed_from_open : brand_model -> qtype -> qtype

  val infer_brand_strict :
    brand_model -> brands -> qtype -> (rtype * qtype) option

  val recminus :
    brand_relation -> (char list * rtype) list -> char list list ->
    (char list * rtype) list

  val diff_record_types :
    brand_model -> brands -> qtype -> (char list list * char list list) option

  val rec_fields_that_are_not_subtype :
    brand_model -> (char list * qtype) list -> (char list * qtype) list ->
    ((char list * qtype) * qtype) list

  val fields_that_are_not_subtype :
    brand_model -> brands -> qtype -> ((char list * qtype) * qtype) list
 end

val zip0 : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option

type qcert_data = QcertData.data

type qcert_type = QcertType.qtype

type location_point = { offset : int; line : int; column : int }

val line : location_point -> int

val column : location_point -> int

module Coq__6 : sig
 type location = { loc_file : char list; loc_start : location_point;
                   loc_end : location_point }
end
include module type of struct include Coq__6 end

val loc_start : location -> location_point

val loc_end : location -> location_point

val dummy_location : location

module Coq__7 : sig
 type provenance =
 | ProvFunc of location * char list
 | ProvClause of location * char list
 | ProvThisContract of location
 | ProvThisClause of location
 | ProvThisState of location
 | ProvLoc of location
end
include module type of struct include Coq__7 end

val dummy_provenance : provenance

val loc_of_provenance : provenance -> location

val string_of_location_point : location_point -> char list

val string_of_location_no_file : location -> char list

type local_name = char list

type namespace_name = char list

type enum_name = char list

type namespace_prefix = namespace_name option

module Coq__8 : sig
 type relative_name = namespace_prefix * local_name
end
include module type of struct include Coq__8 end

type absolute_name = char list

val absolute_name_of_local_name :
  namespace_name -> local_name -> absolute_name

val enum_namespace : namespace_name -> enum_name -> namespace_name

val clause_main_name : local_name

val clause_init_name : local_name

val this_this : char list

val this_contract : char list

val this_state : char list

val this_emit : char list

val this_response : char list

val local_state : char list

val local_emit : char list

val current_time : char list

val options : char list

val accordproject_base_namespace : char list

val accordproject_runtime_namespace : char list

val accordproject_contract_namespace : char list

val accordproject_stdlib_namespace : char list

val accordproject_time_namespace : char list

val accordproject_top_namespace : char list

val accordproject_options_namespace : char list

val accordproject_template_namespace : char list

val default_enum_absolute_name : char list

val default_event_absolute_name : char list

val default_transaction_absolute_name : char list

val default_asset_absolute_name : char list

val default_participant_absolute_name : char list

val default_request_absolute_name : char list

val default_state_absolute_name : char list

val default_contract_absolute_name : char list

val default_clause_absolute_name : char list

val default_error_absolute_name : char list

val default_options : char list

val function_name_in_table : char list option -> char list -> char list

val no_namespace : char list

type 'a import_decl =
| ImportAll of 'a * namespace_name
| ImportSelf of 'a * namespace_name
| ImportName of 'a * namespace_name * local_name

val import_annot : 'a1 import_decl -> 'a1

type 'n extends = 'n option

type limport_decl = provenance import_decl

type rextends = relative_name extends

type aextends = absolute_name extends

type is_abstract = bool

type 'n type_annotation = 'n option

type ('a, 'n) ergo_pattern =
| CaseData of 'a * QcertData.data
| CaseEnum of 'a * 'n
| CaseWildcard of 'a * 'n type_annotation
| CaseLet of 'a * char list * 'n type_annotation
| CaseLetOption of 'a * char list * 'n type_annotation

type lrergo_pattern = (provenance, relative_name) ergo_pattern

type laergo_pattern = (provenance, absolute_name) ergo_pattern

type ergo_unary_operator =
| EOpUMinus
| EOpDot of char list

val toString_ergo_unary_operator : ergo_unary_operator toString

type ergo_binary_operator =
| EOpPlus
| EOpMinus
| EOpMultiply
| EOpDivide
| EOpRemainder
| EOpGe
| EOpGt
| EOpLe
| EOpLt

val toString_ergo_binary_operator : ergo_binary_operator toString

module Coq__9 : sig
 type eerror =
 | ESystemError of provenance * char list
 | EParseError of provenance * char list
 | ECompilationError of provenance * char list
 | ETypeError of provenance * char list
 | ERuntimeError of provenance * char list
end
include module type of struct include Coq__9 end

module Coq__10 : sig
 type ewarning =
 | EWarning of provenance * char list
end
include module type of struct include Coq__10 end

module Coq__11 : sig
 type 'a eresult = ('a * ewarning list, eerror) result
end
include module type of struct include Coq__11 end

val esuccess : 'a1 -> ewarning list -> 'a1 eresult

val efailure : eerror -> 'a1 eresult

val eolift : ('a1 -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult

val eolift_warning :
  (('a1 * ewarning list) -> 'a2 eresult) -> 'a1 eresult -> 'a2 eresult

val elift : ('a1 -> 'a2) -> 'a1 eresult -> 'a2 eresult

val elift2 : ('a1 -> 'a2 -> 'a3) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult

val elift3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult ->
  'a4 eresult

val elift_fold_left :
  ('a1 -> 'a2 -> 'a1 eresult) -> 'a2 list -> 'a1 -> 'a1 eresult

val emaplift : ('a1 -> 'a2 eresult) -> 'a1 list -> 'a2 list eresult

val elift_context_fold_left :
  ('a3 -> 'a1 -> ('a2 * 'a3) eresult) -> 'a1 list -> 'a3 -> ('a2 list * 'a3)
  eresult

val eflatmaplift : ('a1 -> 'a2 list eresult) -> 'a1 list -> 'a2 list eresult

val eresult_of_option : 'a1 option -> eerror -> ewarning list -> 'a1 eresult

val eolift2 :
  ('a1 -> 'a2 -> 'a3 eresult) -> 'a1 eresult -> 'a2 eresult -> 'a3 eresult

val elift_maybe : ('a1 -> 'a1 eresult option) -> 'a1 eresult -> 'a1 eresult

val elift_fail : (eerror -> 'a1 eresult) -> 'a1 eresult -> 'a1 eresult

val elift_both : ('a1 -> 'a2) -> (eerror -> 'a2) -> 'a1 eresult -> 'a2

val elift2_both :
  ('a1 -> 'a2 -> 'a3) -> (eerror -> 'a3) -> 'a1 eresult -> 'a2 eresult -> 'a3

val eerror_of_qerror : provenance -> qerror -> eerror

val eresult_of_qresult : provenance -> 'a1 qresult -> 'a1 eresult

val format_error : char list -> provenance -> char list -> char list

val clause_call_not_on_contract_error : provenance -> 'a1 eresult

val use_contract_not_in_contract_error : provenance -> 'a1 eresult

val call_clause_not_in_contract_error : provenance -> char list -> 'a1 eresult

val not_in_clause_error : provenance -> 'a1 eresult

val case_option_not_on_either_error : provenance -> 'a1 eresult

val set_state_on_non_brand_error : provenance -> char list -> 'a1 eresult

val import_not_found_error : provenance -> char list -> 'a1 eresult

val type_name_not_found_error : provenance -> char list -> 'a1 eresult

val namespace_not_found_error : provenance -> char list -> 'a1 eresult

val variable_name_not_found_error : provenance -> char list -> 'a1 eresult

val enum_name_not_found_error : provenance -> char list -> 'a1 eresult

val function_name_not_found_error : provenance -> char list -> 'a1 eresult

val contract_name_not_found_error : provenance -> char list -> 'a1 eresult

val import_name_not_found_error :
  provenance -> char list -> char list -> 'a1 eresult

val main_parameter_mismatch_error : provenance -> 'a1 eresult

val main_at_least_one_parameter_error : provenance -> 'a1 eresult

val function_not_found_error : provenance -> char list -> 'a1 eresult

val call_params_error : provenance -> char list -> 'a1 eresult

val eval_unary_operator_error :
  provenance -> ergo_unary_operator -> 'a1 eresult

val eval_binary_operator_error :
  provenance -> ergo_binary_operator -> 'a1 eresult

val eval_unary_builtin_error : provenance -> QcertOps.Unary.op -> 'a1 eresult

val eval_binary_builtin_error :
  provenance -> QcertOps.Binary.op -> 'a1 eresult

val eval_if_not_boolean_error : provenance -> 'a1 eresult

val eval_foreach_not_on_array_error : provenance -> 'a1 eresult

val template_type_not_found_error : provenance -> 'a1 eresult

val more_than_one_template_type_error : provenance -> char list -> 'a1 eresult

val no_ergo_module_error : provenance -> 'a1 eresult

val built_in_function_not_found_error : provenance -> char list -> 'a1 eresult

val built_in_function_without_body_error :
  provenance -> char list -> 'a1 eresult

val enforce_error_content : provenance -> char list -> QcertData.data

val default_match_error_content : provenance -> data

val should_have_one_contract_error : provenance -> 'a1 eresult

val this_in_calculus_error : provenance -> 'a1 eresult

val contract_in_calculus_error : provenance -> 'a1 eresult

val clause_in_calculus_error : provenance -> 'a1 eresult

val operator_in_calculus_error : provenance -> 'a1 eresult

val state_in_calculus_error : provenance -> 'a1 eresult

val text_in_calculus_error : provenance -> 'a1 eresult

val complex_foreach_in_calculus_error : provenance -> 'a1 eresult

val print_in_calculus_error : provenance -> 'a1 eresult

val function_not_inlined_error :
  provenance -> char list -> char list -> 'a1 eresult

val function_in_group_not_inlined_error :
  provenance -> char list -> char list -> 'a1 eresult

val no_duplicates_with_err :
  char list list -> 'a1 -> (char list option -> eerror) -> 'a1 eresult

val duplicate_function_params_error :
  provenance -> char list -> char list option -> eerror

val duplicate_function_params_check :
  provenance -> char list -> char list list -> 'a1 -> 'a1 eresult

val duplicate_clause_for_request_error :
  provenance -> char list option -> eerror

val duplicate_clause_for_request_check :
  provenance -> char list list -> 'a1 -> 'a1 eresult

val warning_no_else : provenance -> ewarning

val warning_global_shadowing : provenance -> char list -> ewarning

module Coq__13 : sig
 type ('a, 'n) cto_type =
 | CTOBoolean of 'a
 | CTOString of 'a
 | CTODouble of 'a
 | CTOLong of 'a
 | CTOInteger of 'a
 | CTODateTime of 'a
 | CTOClassRef of 'a * 'n
 | CTOOption of 'a * ('a, 'n) cto_type
 | CTOArray of 'a * ('a, 'n) cto_type
end
include module type of struct include Coq__13 end

type ('a, 'n) cto_declaration_desc =
| CTOEnum of char list list
| CTOTransaction of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list
| CTOConcept of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list
| CTOEvent of is_abstract * 'n extends * (char list * ('a, 'n) cto_type) list
| CTOAsset of is_abstract * 'n extends * (char list * ('a, 'n) cto_type) list
| CTOParticipant of is_abstract * 'n extends
   * (char list * ('a, 'n) cto_type) list

type ('a, 'n) cto_declaration = { cto_declaration_annot : 'a;
                                  cto_declaration_name : local_name;
                                  cto_declaration_type : ('a, 'n)
                                                         cto_declaration_desc }

val cto_declaration_annot : ('a1, 'a2) cto_declaration -> 'a1

val cto_declaration_name : ('a1, 'a2) cto_declaration -> local_name

val cto_declaration_type :
  ('a1, 'a2) cto_declaration -> ('a1, 'a2) cto_declaration_desc

type ('a, 'n) cto_package = { cto_package_annot : 'a;
                              cto_package_file : char list;
                              cto_package_prefix : char list;
                              cto_package_namespace : namespace_name;
                              cto_package_imports : 'a import_decl list;
                              cto_package_declarations : ('a, 'n)
                                                         cto_declaration list }

val cto_package_annot : ('a1, 'a2) cto_package -> 'a1

val cto_package_file : ('a1, 'a2) cto_package -> char list

val cto_package_prefix : ('a1, 'a2) cto_package -> char list

val cto_package_namespace : ('a1, 'a2) cto_package -> namespace_name

val cto_package_imports : ('a1, 'a2) cto_package -> 'a1 import_decl list

val cto_package_declarations :
  ('a1, 'a2) cto_package -> ('a1, 'a2) cto_declaration list

type lrcto_type = (provenance, relative_name) cto_type

type lrcto_declaration_desc = (provenance, relative_name) cto_declaration_desc

type lrcto_declaration = (provenance, relative_name) cto_declaration

type lrcto_package = (provenance, relative_name) cto_package

module Coq__15 : sig
 type ('a, 'n) ergo_type =
 | ErgoTypeAny of 'a
 | ErgoTypeNothing of 'a
 | ErgoTypeUnit of 'a
 | ErgoTypeBoolean of 'a
 | ErgoTypeString of 'a
 | ErgoTypeDouble of 'a
 | ErgoTypeLong of 'a
 | ErgoTypeInteger of 'a
 | ErgoTypeDateTimeFormat of 'a
 | ErgoTypeDateTime of 'a
 | ErgoTypeDuration of 'a
 | ErgoTypePeriod of 'a
 | ErgoTypeClassRef of 'a * 'n
 | ErgoTypeOption of 'a * ('a, 'n) ergo_type
 | ErgoTypeRecord of 'a * (char list * ('a, 'n) ergo_type) list
 | ErgoTypeArray of 'a * ('a, 'n) ergo_type
 | ErgoTypeSum of 'a * ('a, 'n) ergo_type * ('a, 'n) ergo_type
end
include module type of struct include Coq__15 end

type ('a, 'n) ergo_type_signature = { type_signature_annot : 'a;
                                      type_signature_params : (char list * ('a,
                                                              'n) ergo_type)
                                                              list;
                                      type_signature_output : ('a, 'n)
                                                              ergo_type option;
                                      type_signature_emits : ('a, 'n)
                                                             ergo_type option }

val type_signature_annot : ('a1, 'a2) ergo_type_signature -> 'a1

val type_signature_params :
  ('a1, 'a2) ergo_type_signature -> (char list * ('a1, 'a2) ergo_type) list

val type_signature_output :
  ('a1, 'a2) ergo_type_signature -> ('a1, 'a2) ergo_type option

val type_signature_emits :
  ('a1, 'a2) ergo_type_signature -> ('a1, 'a2) ergo_type option

type ('a, 'n) ergo_type_declaration_desc =
| ErgoTypeEnum of char list list
| ErgoTypeTransaction of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeConcept of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeEvent of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeAsset of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeParticipant of is_abstract * 'n extends
   * (char list * ('a, 'n) ergo_type) list
| ErgoTypeGlobal of ('a, 'n) ergo_type
| ErgoTypeFunction of ('a, 'n) ergo_type_signature
| ErgoTypeContract of ('a, 'n) ergo_type * ('a, 'n) ergo_type
   * (char list * ('a, 'n) ergo_type_signature) list

module Coq__18 : sig
 type ('a, 'n) ergo_type_declaration = { type_declaration_annot : 'a;
                                         type_declaration_name : local_name;
                                         type_declaration_type : ('a, 'n)
                                                                 ergo_type_declaration_desc }
end
include module type of struct include Coq__18 end

val type_declaration_annot : ('a1, 'a2) ergo_type_declaration -> 'a1

val type_declaration_name : ('a1, 'a2) ergo_type_declaration -> local_name

val type_declaration_type :
  ('a1, 'a2) ergo_type_declaration -> ('a1, 'a2) ergo_type_declaration_desc

val type_declaration_is_abstract :
  ('a1, 'a2) ergo_type_declaration_desc -> is_abstract

val type_declaration_is_enum :
  ('a1, 'a2) ergo_type_declaration_desc -> char list list option

type lrergo_type = (provenance, relative_name) ergo_type

type lrergo_type_signature = (provenance, relative_name) ergo_type_signature

type lrergo_type_declaration_desc =
  (provenance, relative_name) ergo_type_declaration_desc

type lrergo_type_declaration =
  (provenance, relative_name) ergo_type_declaration

type laergo_type = (provenance, absolute_name) ergo_type

type laergo_type_signature = (provenance, absolute_name) ergo_type_signature

module Coq__14 : sig
 type laergo_type_declaration =
   (provenance, absolute_name) ergo_type_declaration
end
include module type of struct include Coq__14 end

type laergo_type_declaration_desc =
  (provenance, absolute_name) ergo_type_declaration_desc

val lift_default_emits_type : provenance -> laergo_type option -> laergo_type

val lift_default_state_type : provenance -> laergo_type option -> laergo_type

val default_throws_type : provenance -> laergo_type

val mk_success_type :
  provenance -> laergo_type -> laergo_type -> laergo_type -> laergo_type

val mk_error_type : provenance -> laergo_type -> laergo_type

val mk_output_type : provenance -> laergo_type -> laergo_type -> laergo_type

val fix_nothing : absolute_name -> (absolute_name * absolute_name) list

val fix_transaction : absolute_name -> (absolute_name * char list) list

val fix_event : absolute_name -> (absolute_name * char list) list

val fix_asset : absolute_name -> (absolute_name * char list) list

val fix_participant : absolute_name -> (absolute_name * char list) list

val extends_rel :
  (absolute_name -> (absolute_name * absolute_name) list) -> absolute_name ->
  absolute_name extends -> (absolute_name * absolute_name) list

val type_declaration_desc_extend_rel :
  absolute_name -> laergo_type_declaration_desc ->
  (absolute_name * absolute_name) list

val type_declaration_extend_rel :
  laergo_type_declaration -> (absolute_name * absolute_name) list

val type_name_of_type : laergo_type -> char list option

val label_of_decl : laergo_type_declaration -> char list

val name_of_decl : laergo_type_declaration -> char list

val decls_table :
  laergo_type_declaration list -> (char list * laergo_type_declaration) list

val edge_of_decl :
  (char list * laergo_type_declaration) list -> laergo_type_declaration ->
  laergo_type_declaration * laergo_type_declaration list

val graph_of_decls :
  laergo_type_declaration list ->
  (laergo_type_declaration * laergo_type_declaration list) list

val sort_decls : laergo_type_declaration list -> laergo_type_declaration list

val sort_given_topo_order :
  laergo_type_declaration list -> ('a1 -> char list) -> 'a1 list -> 'a1 list

type enum_flag =
| EnumNone
| EnumValue of data
| EnumType of (char list * data) list

type name_table = (local_name * (absolute_name * enum_flag)) list

type namespace_table = { namespace_table_types : name_table;
                         namespace_table_constants : name_table;
                         namespace_table_functions : name_table;
                         namespace_table_contracts : name_table }

val namespace_table_types : namespace_table -> name_table

val namespace_table_constants : namespace_table -> name_table

val namespace_table_functions : namespace_table -> name_table

val namespace_table_contracts : namespace_table -> name_table

val empty_namespace_table : namespace_table

val import_one_type_to_namespace_table :
  local_name -> absolute_name -> namespace_table

val import_one_enum_type_to_namespace_table :
  local_name -> absolute_name -> (char list * data) list -> namespace_table

val import_one_constant_to_namespace_table :
  local_name -> absolute_name -> namespace_table

val namespace_table_app :
  namespace_table -> namespace_table -> namespace_table

val lookup_type_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_constant_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_econstant_name :
  provenance -> namespace_table -> local_name -> (absolute_name * data)
  eresult

val lookup_function_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val lookup_contract_name :
  provenance -> namespace_table -> local_name -> absolute_name eresult

val add_type_to_namespace_table :
  local_name -> absolute_name -> enum_flag -> namespace_table ->
  namespace_table

val add_constant_to_namespace_table :
  local_name -> absolute_name -> enum_flag -> namespace_table ->
  namespace_table

val add_constants_to_namespace_table :
  (local_name * (absolute_name * enum_flag)) list -> namespace_table ->
  namespace_table

val hide_constant_from_namespace_table :
  local_name -> namespace_table -> namespace_table

val add_function_to_namespace_table :
  local_name -> absolute_name -> namespace_table -> namespace_table

val add_contract_to_namespace_table :
  local_name -> absolute_name -> namespace_table -> namespace_table

type abstract_ctxt = char list list

type namespace_ctxt = { namespace_ctxt_modules : (namespace_name * namespace_table)
                                                 list;
                        namespace_ctxt_namespace : namespace_name;
                        namespace_ctxt_current_module : namespace_table;
                        namespace_ctxt_current_in_scope : namespace_table;
                        namespace_ctxt_abstract : abstract_ctxt }

val namespace_ctxt_modules :
  namespace_ctxt -> (namespace_name * namespace_table) list

val namespace_ctxt_namespace : namespace_ctxt -> namespace_name

val namespace_ctxt_current_module : namespace_ctxt -> namespace_table

val namespace_ctxt_current_in_scope : namespace_ctxt -> namespace_table

val namespace_ctxt_abstract : namespace_ctxt -> abstract_ctxt

val empty_namespace_ctxt : namespace_name -> namespace_ctxt

val update_namespace_context_modules :
  namespace_ctxt -> namespace_name -> (namespace_table -> namespace_table) ->
  namespace_ctxt

val update_namespace_context_current_both :
  namespace_ctxt -> (namespace_table -> namespace_table) -> namespace_ctxt

val update_namespace_context_abstract :
  namespace_ctxt -> abstract_ctxt -> namespace_ctxt

val add_type_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  enum_flag -> namespace_ctxt

val add_constant_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> enum_flag ->
  absolute_name -> namespace_ctxt

val add_function_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  namespace_ctxt

val add_contract_to_namespace_ctxt :
  namespace_ctxt -> namespace_name -> local_name -> absolute_name ->
  namespace_ctxt

val add_type_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> enum_flag -> namespace_ctxt

val add_constant_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> enum_flag -> namespace_ctxt

val add_econstants_to_namespace_ctxt_current :
  namespace_ctxt -> namespace_name ->
  (local_name * (absolute_name * enum_flag)) list -> namespace_ctxt

val hide_constant_from_namespace_ctxt_current :
  namespace_ctxt -> local_name -> namespace_ctxt

val hide_constants_from_namespace_ctxt_current :
  namespace_ctxt -> local_name list -> namespace_ctxt

val add_function_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt

val add_contract_to_namespace_ctxt_current :
  namespace_ctxt -> local_name -> absolute_name -> namespace_ctxt

val new_namespace_scope : namespace_ctxt -> namespace_name -> namespace_ctxt

val local_namespace_scope : namespace_ctxt -> namespace_name -> namespace_ctxt

val verify_name :
  (provenance -> namespace_table -> local_name -> 'a1 eresult) -> provenance
  -> namespace_ctxt -> namespace_name -> local_name -> 'a1 eresult

val verify_type_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_constant_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_econstant_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  (absolute_name * data) eresult

val verify_function_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val verify_contract_name :
  provenance -> namespace_ctxt -> namespace_name -> local_name ->
  absolute_name eresult

val resolve_type_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_constant_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_econstant_name :
  provenance -> namespace_ctxt -> relative_name -> (absolute_name * data)
  eresult

val resolve_all_constant_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_function_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

val resolve_contract_name :
  provenance -> namespace_ctxt -> relative_name -> absolute_name eresult

module Coq__16 : sig
 type ('a, 'x, 'n) ergo_expr =
 | EThis of 'a
 | EThisContract of 'a
 | EThisClause of 'a
 | EThisState of 'a
 | EVar of 'a * 'n
 | EConst of 'a * data
 | EText of 'a * ('a, 'x, 'n) ergo_expr list
 | ENone of 'a
 | ESome of 'a * ('a, 'x, 'n) ergo_expr
 | EArray of 'a * ('a, 'x, 'n) ergo_expr list
 | EUnaryOperator of 'a * ergo_unary_operator * ('a, 'x, 'n) ergo_expr
 | EBinaryOperator of 'a * ergo_binary_operator * ('a, 'x, 'n) ergo_expr
    * ('a, 'x, 'n) ergo_expr
 | EUnaryBuiltin of 'a * QcertOps.Unary.op * ('a, 'x, 'n) ergo_expr
 | EBinaryBuiltin of 'a * QcertOps.Binary.op * ('a, 'x, 'n) ergo_expr
    * ('a, 'x, 'n) ergo_expr
 | EIf of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr
    * ('a, 'x, 'n) ergo_expr
 | ELet of 'a * char list * ('x, 'n) ergo_type option
    * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr
 | EPrint of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr
 | ERecord of 'a * (char list * ('a, 'x, 'n) ergo_expr) list
 | ENew of 'a * 'n * (char list * ('a, 'x, 'n) ergo_expr) list
 | ECallFun of 'a * 'n * ('a, 'x, 'n) ergo_expr list
 | ECallFunInGroup of 'a * 'n * char list * ('a, 'x, 'n) ergo_expr list
 | EMatch of 'a * ('a, 'x, 'n) ergo_expr
    * (('a, 'n) ergo_pattern * ('a, 'x, 'n) ergo_expr) list
    * ('a, 'x, 'n) ergo_expr
 | EForeach of 'a * (char list * ('a, 'x, 'n) ergo_expr) list
    * ('a, 'x, 'n) ergo_expr option * ('a, 'x, 'n) ergo_expr
end
include module type of struct include Coq__16 end

val expr_annot : ('a1, 'a2, 'a3) ergo_expr -> 'a1

module Coq__17 : sig
 type ('a, 'x, 'n) ergo_stmt =
 | SReturn of 'a * ('a, 'x, 'n) ergo_expr
 | SFunReturn of 'a * ('a, 'x, 'n) ergo_expr
 | SThrow of 'a * ('a, 'x, 'n) ergo_expr
 | SCallClause of 'a * ('a, 'x, 'n) ergo_expr * char list
    * ('a, 'x, 'n) ergo_expr list
 | SCallContract of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr list
 | SSetState of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
 | SSetStateDot of 'a * char list * ('a, 'x, 'n) ergo_expr
    * ('a, 'x, 'n) ergo_stmt
 | SEmit of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
 | SLet of 'a * char list * ('a, 'n) ergo_type option
    * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
 | SPrint of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
 | SIf of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
    * ('a, 'x, 'n) ergo_stmt
 | SEnforce of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt option
    * ('a, 'x, 'n) ergo_stmt
 | SMatch of 'a * ('a, 'x, 'n) ergo_expr
    * (('a, 'n) ergo_pattern * ('a, 'x, 'n) ergo_stmt) list
    * ('a, 'x, 'n) ergo_stmt
end
include module type of struct include Coq__17 end

module Coq__19 : sig
 type ('a, 'x, 'n) ergo_function = { function_annot : 'a;
                                     function_sig : ('a, 'n)
                                                    ergo_type_signature;
                                     function_body : ('a, 'x, 'n) ergo_expr
                                                     option }
end
include module type of struct include Coq__19 end

val function_annot : ('a1, 'a2, 'a3) ergo_function -> 'a1

val function_sig :
  ('a1, 'a2, 'a3) ergo_function -> ('a1, 'a3) ergo_type_signature

val function_body :
  ('a1, 'a2, 'a3) ergo_function -> ('a1, 'a2, 'a3) ergo_expr option

type ('a, 'x, 'n) ergo_clause = { clause_annot : 'a;
                                  clause_name : local_name;
                                  clause_sig : ('a, 'n) ergo_type_signature;
                                  clause_body : ('a, 'x, 'n) ergo_stmt option }

val clause_annot : ('a1, 'a2, 'a3) ergo_clause -> 'a1

val clause_name : ('a1, 'a2, 'a3) ergo_clause -> local_name

val clause_sig : ('a1, 'a2, 'a3) ergo_clause -> ('a1, 'a3) ergo_type_signature

val clause_body :
  ('a1, 'a2, 'a3) ergo_clause -> ('a1, 'a2, 'a3) ergo_stmt option

module Coq__20 : sig
 type ('a, 'x, 'n) ergo_contract = { contract_annot : 'a;
                                     contract_template : ('a, 'n) ergo_type;
                                     contract_state : ('a, 'n) ergo_type
                                                      option;
                                     contract_clauses : ('a, 'x, 'n)
                                                        ergo_clause list }
end
include module type of struct include Coq__20 end

val contract_annot : ('a1, 'a2, 'a3) ergo_contract -> 'a1

val contract_template : ('a1, 'a2, 'a3) ergo_contract -> ('a1, 'a3) ergo_type

val contract_state :
  ('a1, 'a2, 'a3) ergo_contract -> ('a1, 'a3) ergo_type option

val contract_clauses :
  ('a1, 'a2, 'a3) ergo_contract -> ('a1, 'a2, 'a3) ergo_clause list

type ('a, 'x, 'n) ergo_declaration =
| DNamespace of 'a * namespace_name
| DImport of 'a * 'a import_decl
| DType of 'a * ('a, 'n) ergo_type_declaration
| DStmt of 'a * ('a, 'x, 'n) ergo_stmt
| DConstant of 'a * local_name * ('a, 'n) ergo_type option
   * ('a, 'x, 'n) ergo_expr
| DFunc of 'a * local_name * ('a, 'x, 'n) ergo_function
| DContract of 'a * local_name * ('a, 'x, 'n) ergo_contract
| DSetContract of 'a * 'n * ('a, 'x, 'n) ergo_expr

type ('a, 'x, 'n) ergo_module = { module_annot : 'a; module_file : char list;
                                  module_prefix : char list;
                                  module_namespace : namespace_name;
                                  module_declarations : ('a, 'x, 'n)
                                                        ergo_declaration list }

val module_annot : ('a1, 'a2, 'a3) ergo_module -> 'a1

val module_file : ('a1, 'a2, 'a3) ergo_module -> char list

val module_prefix : ('a1, 'a2, 'a3) ergo_module -> char list

val module_namespace : ('a1, 'a2, 'a3) ergo_module -> namespace_name

val module_declarations :
  ('a1, 'a2, 'a3) ergo_module -> ('a1, 'a2, 'a3) ergo_declaration list

type ('a, 'x, 'n) ergo_input =
| InputErgo of ('a, 'x, 'n) ergo_module
| InputCTO of ('a, 'n) cto_package

type ('a, 'x) rergo_expr = ('a, 'x, relative_name) ergo_expr

type ('a, 'x) rergo_stmt = ('a, 'x, relative_name) ergo_stmt

type lrergo_expr = (provenance, provenance, relative_name) ergo_expr

type lrergo_stmt = (provenance, provenance, relative_name) ergo_stmt

type lrergo_function = (provenance, provenance, relative_name) ergo_function

type lrergo_clause = (provenance, provenance, relative_name) ergo_clause

type lrergo_contract = (provenance, provenance, relative_name) ergo_contract

type lrergo_declaration =
  (provenance, provenance, relative_name) ergo_declaration

type lrergo_module = (provenance, provenance, relative_name) ergo_module

type lrergo_input = (provenance, provenance, relative_name) ergo_input

type laergo_expr = (provenance, provenance, absolute_name) ergo_expr

type laergo_stmt = (provenance, provenance, absolute_name) ergo_stmt

type laergo_function = (provenance, provenance, absolute_name) ergo_function

type laergo_clause = (provenance, provenance, absolute_name) ergo_clause

type laergo_contract = (provenance, provenance, absolute_name) ergo_contract

type laergo_declaration =
  (provenance, provenance, absolute_name) ergo_declaration

type laergo_module = (provenance, provenance, absolute_name) ergo_module

val lookup_clause_signatures :
  laergo_clause list -> (local_name * (provenance, absolute_name)
  ergo_type_signature) list

val lookup_contract_signatures :
  (provenance, provenance, absolute_name) ergo_contract ->
  (local_name * (provenance, absolute_name) ergo_type_signature) list

val contract_of_declaration :
  laergo_declaration -> (absolute_name * laergo_contract) option

val lookup_contracts_in_declarations :
  laergo_declaration list -> (absolute_name * laergo_contract) list

val lookup_single_contract_in_declarations :
  provenance -> laergo_declaration list -> (absolute_name * laergo_contract)
  eresult

val lookup_single_contract :
  laergo_module -> (absolute_name * laergo_contract) eresult

val get_type_decls : laergo_declaration list -> laergo_type_declaration list

val module_get_type_decls : laergo_module -> laergo_type_declaration list

val modules_get_type_decls :
  laergo_module list -> laergo_type_declaration list

val either_from_enum_values : char list list -> (char list * data) list

val globals_from_enum :
  provenance -> (char list * char list list) ->
  ((char list * laergo_expr) * data) list

val sReturnEmpty : 'a1 -> ('a1, 'a2) rergo_stmt

val eFunReturnEmpty : 'a1 -> ('a1, 'a2) rergo_expr

val eOptionalDot :
  'a1 -> char list -> ('a1, 'a2) rergo_expr -> ('a1, 'a2, relative_name)
  ergo_expr

val eOptionalDefault :
  'a1 -> ('a1, 'a2) rergo_expr -> ('a1, 'a2) rergo_expr -> ('a1, 'a2,
  relative_name) ergo_expr

type ergo_nnrc_expr = QcertCodeGen.nnrc_expr

type ergo_nnrc_type = qcert_type

type ergo_nnrc_lambda = { lambdan_provenance : provenance;
                          lambdan_params : (char list * ergo_nnrc_type) list;
                          lambdan_output : ergo_nnrc_type;
                          lambdan_body : ergo_nnrc_expr }

val lambdan_body : brand_model -> ergo_nnrc_lambda -> ergo_nnrc_expr

type ergo_nnrc_function_table = { function_tablen_provenance : provenance;
                                  function_tablen_funs : (char list * ergo_nnrc_lambda)
                                                         list }

val function_tablen_funs :
  brand_model -> ergo_nnrc_function_table -> (char list * ergo_nnrc_lambda)
  list

type ergo_nnrc_declaration =
| DNFunc of char list * ergo_nnrc_lambda
| DNFuncTable of char list * ergo_nnrc_function_table

type ergo_nnrc_module = { modulen_provenance : provenance;
                          modulen_namespace : char list;
                          modulen_declarations : ergo_nnrc_declaration list }

val modulen_provenance : brand_model -> ergo_nnrc_module -> provenance

val modulen_namespace : brand_model -> ergo_nnrc_module -> char list

val modulen_declarations :
  brand_model -> ergo_nnrc_module -> ergo_nnrc_declaration list

module Coq__12 : sig
 type result_file = { res_contract_name : char list option;
                      res_file : char list; res_content : nstring }
end
include module type of struct include Coq__12 end

val print_brand : namespace_ctxt -> char list -> char list

val print_multiple_brands : namespace_ctxt -> char list list -> char list

val unpack_output :
  qcert_data -> ((qcert_data * qcert_data list) * qcert_data) option

val fmt_nl : char list

val string_of_enum : namespace_ctxt -> qcert_data -> char list

val string_of_data : namespace_ctxt -> qcert_data -> char list

val rtype_to_string : namespace_ctxt -> rtype_UU2080_ -> char list

val qcert_type_to_string :
  brand_model -> namespace_ctxt -> qcert_type -> char list

val string_of_result_type :
  brand_model -> namespace_ctxt -> qcert_type option -> char list

val unpack_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> eerror

val unpack_failure_type :
  brand_model -> namespace_ctxt -> qcert_type -> qcert_type eresult

val unpack_success_type :
  brand_model -> namespace_ctxt -> qcert_type -> ewarning list ->
  ((qcert_type * qcert_type) * qcert_type) eresult

val unpack_output_type :
  brand_model -> namespace_ctxt -> qcert_type -> ewarning list ->
  (((qcert_type * qcert_type) * qcert_type) * qcert_type) eresult

val string_of_response :
  brand_model -> namespace_ctxt -> qcert_data -> qcert_type option ->
  char list

val string_of_emits :
  brand_model -> namespace_ctxt -> qcert_data list -> qcert_type option ->
  char list

val string_of_state :
  brand_model -> namespace_ctxt -> qcert_data option -> qcert_data ->
  qcert_type option -> char list

val string_of_typed_data :
  brand_model -> namespace_ctxt -> qcert_data option -> qcert_data ->
  qcert_type option -> char list

val string_of_typed_result :
  brand_model -> namespace_ctxt -> qcert_data option -> (qcert_type
  option * qcert_data option) -> char list

type expand_hierarchy = char list list

type expanded_type =
| ClassObjectType of (char list * laergo_type) list
| ClassEnumType of char list list

type expand_ctxt = (char list * (expand_hierarchy * expanded_type)) list

val ergo_expand_class_object_extends :
  expand_ctxt -> absolute_name -> absolute_name -> (char list * laergo_type)
  list -> expand_ctxt

val ergo_expand_class_enum_extends :
  expand_ctxt -> absolute_name -> absolute_name -> char list list ->
  expand_ctxt

val ergo_decl_expand_extends :
  expand_ctxt -> absolute_name -> laergo_type_declaration_desc -> expand_ctxt

val ergo_expand_extends_in_declarations :
  laergo_type_declaration list -> expand_ctxt

val ergo_hierarchy_from_expand : expand_ctxt -> (char list * char list) list

val ergo_type_to_qcert_type : brand_relation -> laergo_type -> qcert_type

val enum_type_of_list : brand_relation -> char list list -> qcert_type

val ergo_ctype_from_expanded_type :
  brand_relation -> expanded_type -> qcert_type

val ergo_ctype_decl_from_expand :
  brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls

val brand_relation_maybe :
  (char list * char list) list -> QcertType.tbrand_relation eresult

val mk_model_type_decls :
  brand_relation -> expand_ctxt -> QcertType.tbrand_context_decls

val brand_model_of_declarations :
  laergo_type_declaration list ->
  (QcertType.tbrand_model * laergo_type_declaration list) eresult

type ergoc_expr = laergo_expr

type sigc = { sigc_params : (char list * laergo_type) list;
              sigc_output : laergo_type option }

val sigc_params : sigc -> (char list * laergo_type) list

val sigc_output : sigc -> laergo_type option

type ergoc_function = { functionc_annot : provenance; functionc_sig : 
                        sigc; functionc_body : ergoc_expr option }

val functionc_annot : ergoc_function -> provenance

val functionc_sig : ergoc_function -> sigc

val functionc_body : ergoc_function -> ergoc_expr option

val bodyc_annot : ergoc_function -> provenance

type ergoc_contract = { contractc_annot : provenance;
                        contractc_template : laergo_type;
                        contractc_state : laergo_type option;
                        contractc_clauses : (local_name * ergoc_function) list }

val contractc_annot : ergoc_contract -> provenance

val contractc_template : ergoc_contract -> laergo_type

val contractc_state : ergoc_contract -> laergo_type option

val contractc_clauses : ergoc_contract -> (local_name * ergoc_function) list

type ergoc_declaration =
| DCExpr of provenance * ergoc_expr
| DCConstant of provenance * absolute_name * laergo_type option * ergoc_expr
| DCFunc of provenance * absolute_name * ergoc_function
| DCContract of provenance * absolute_name * ergoc_contract

type ergoc_module = { modulec_annot : provenance;
                      modulec_namespace : char list;
                      modulec_declarations : ergoc_declaration list }

val modulec_annot : ergoc_module -> provenance

val modulec_namespace : ergoc_module -> char list

val modulec_declarations : ergoc_module -> ergoc_declaration list

val lookup_clausec_request_signatures :
  (local_name * ergoc_function) list -> (local_name * sigc) list

val lookup_contractc_request_signatures :
  ergoc_contract -> (local_name * sigc) list

type eval_context = { eval_context_global_env : (char list * qcert_data) list;
                      eval_context_local_env : (char list * qcert_data) list }

val eval_context_global_env : eval_context -> (char list * qcert_data) list

val eval_context_local_env : eval_context -> (char list * qcert_data) list

val eval_context_update_global_env :
  eval_context -> char list -> qcert_data -> eval_context

val eval_context_update_local_env :
  eval_context -> char list -> qcert_data -> eval_context

val empty_eval_context : eval_context

type tlaergo_pattern = (provenance * qcert_type, absolute_name) ergo_pattern

type tlaergo_expr =
  (provenance * qcert_type, provenance, absolute_name) ergo_expr

type ergoct_expr = tlaergo_expr

val exprct_type_annot : brand_model -> ergoct_expr -> qcert_type

type sigct = { sigct_params : (char list * qcert_type) list;
               sigct_output : qcert_type }

val sigct_params : brand_model -> sigct -> (char list * qcert_type) list

val sigct_output : brand_model -> sigct -> qcert_type

type ergoct_function = { functionct_annot : provenance;
                         functionct_sig : sigct;
                         functionct_body : ergoct_expr option }

val functionct_annot : brand_model -> ergoct_function -> provenance

val functionct_sig : brand_model -> ergoct_function -> sigct

val functionct_body : brand_model -> ergoct_function -> ergoct_expr option

type ergoct_contract = { contractct_annot : provenance;
                         contractct_clauses : (local_name * ergoct_function)
                                              list }

val contractct_annot : brand_model -> ergoct_contract -> provenance

val contractct_clauses :
  brand_model -> ergoct_contract -> (local_name * ergoct_function) list

type ergoct_declaration =
| DCTExpr of (provenance * qcert_type) * ergoct_expr
| DCTConstant of (provenance * qcert_type) * absolute_name
   * laergo_type option * ergoct_expr
| DCTFunc of provenance * absolute_name * ergoct_function
| DCTContract of provenance * absolute_name * ergoct_contract

val ergoct_declaration_type :
  brand_model -> ergoct_declaration -> qcert_type option

type ergoct_module = { modulect_annot : provenance;
                       modulect_namespace : char list;
                       modulect_declarations : ergoct_declaration list }

val modulect_annot : brand_model -> ergoct_module -> provenance

val modulect_namespace : brand_model -> ergoct_module -> char list

val modulect_declarations :
  brand_model -> ergoct_module -> ergoct_declaration list

val ergo_unary_builtin_eval :
  brand_model -> provenance -> unary_op -> qcert_data -> qcert_data eresult

val ergo_binary_builtin_eval :
  brand_model -> provenance -> binary_op -> qcert_data -> qcert_data ->
  qcert_data eresult

val ergoct_eval_expr :
  brand_model -> eval_context -> ergoct_expr -> qcert_data eresult

val ergoct_eval_decl :
  brand_model -> eval_context -> ergoct_declaration ->
  (eval_context * qcert_data option) eresult

type type_context = { type_context_global_env : (char list * qcert_type) list;
                      type_context_local_env : (char list * qcert_type) list }

val type_context_global_env :
  brand_relation -> type_context -> (char list * qcert_type) list

val type_context_local_env :
  brand_relation -> type_context -> (char list * qcert_type) list

val type_context_update_global_env :
  brand_relation -> type_context -> char list -> qcert_type -> type_context

val type_context_update_local_env :
  brand_relation -> type_context -> char list -> qcert_type -> type_context

val type_context_set_local_env :
  brand_relation -> type_context -> (char list * qcert_type) list ->
  type_context

val empty_type_context : brand_relation -> type_context

val empty_rec_type : brand_model -> qcert_type

val ergo_format_unop_error :
  brand_model -> namespace_ctxt -> unary_op -> qcert_type -> char list

val ergo_format_binop_error :
  brand_model -> namespace_ctxt -> binary_op -> qcert_type -> qcert_type ->
  char list

val ergo_format_unary_operator_dispatch_error :
  brand_model -> namespace_ctxt -> ergo_unary_operator -> qcert_type ->
  char list

val ergo_format_binary_operator_dispatch_error :
  brand_model -> namespace_ctxt -> ergo_binary_operator -> qcert_type ->
  qcert_type -> char list

val ergo_format_new_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> char list

val ergo_format_clause_return_fallback_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> qcert_type ->
  char list

val ergo_format_clause_return_component_error :
  brand_model -> namespace_ctxt -> char list -> char list -> char list ->
  qcert_type -> qcert_type -> char list

val ergo_format_clause_return_normal_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> qcert_type ->
  (((qcert_type * qcert_type) * qcert_type) * qcert_type) ->
  (((qcert_type * qcert_type) * qcert_type) * qcert_type) -> char list

val ergo_format_clause_return_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> qcert_type ->
  char list

val ergo_format_function_return_error :
  brand_model -> namespace_ctxt -> char list -> qcert_type -> qcert_type ->
  char list

val make_unary_operator_criteria :
  brand_model -> unary_op -> namespace_ctxt -> provenance -> QcertType.qtype
  -> qcert_type eresult

val make_binary_operator_criteria :
  brand_model -> binary_op -> namespace_ctxt -> provenance -> QcertType.qtype
  -> QcertType.qtype -> qcert_type eresult

type unary_dispatch_spec =
  (namespace_ctxt -> provenance -> qcert_type -> qcert_type
  eresult) * (provenance -> qcert_type -> ergoct_expr -> ergoct_expr)

type unary_dispatch_table = unary_dispatch_spec list

val make_unary_operator_fun :
  brand_model -> QcertOps.Unary.op -> provenance -> qcert_type ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_unary_operator : brand_model -> unary_op -> unary_dispatch_spec

val make_nat_minus_fun :
  brand_model -> provenance -> QcertType.qtype ->
  (provenance * QcertType.qtype, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_nat_minus_criteria :
  brand_model -> namespace_ctxt -> provenance -> QcertType.qtype ->
  qcert_type eresult

val make_nat_minus_operator : brand_model -> unary_dispatch_spec

val make_dot_criteria :
  brand_model -> char list -> namespace_ctxt -> provenance -> QcertType.qtype
  -> qcert_type eresult

val make_dot_operator : brand_model -> char list -> unary_dispatch_spec

val make_unbrand_dot_fun :
  brand_model -> char list -> provenance -> qcert_type ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_unbrand_dot_criteria :
  brand_model -> char list -> namespace_ctxt -> provenance -> QcertType.qtype
  -> qcert_type eresult

val make_unbrand_dot_operator :
  brand_model -> char list -> unary_dispatch_spec

val unary_operator_dispatch_table :
  brand_model -> ergo_unary_operator -> unary_dispatch_table

val try_unary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> eerror ->
  ergo_unary_operator -> unary_dispatch_table -> ergoct_expr -> ergoct_expr
  eresult

val unary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_unary_operator ->
  ergoct_expr -> ergoct_expr eresult

type binary_dispatch_spec =
  (namespace_ctxt -> provenance -> qcert_type -> qcert_type -> qcert_type
  eresult) * (provenance -> qcert_type -> ergoct_expr -> ergoct_expr ->
  ergoct_expr)

type binary_dispatch_table = binary_dispatch_spec list

val make_binary_operator_fun :
  brand_model -> QcertOps.Binary.op -> provenance -> qcert_type ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_binary_operator : brand_model -> binary_op -> binary_dispatch_spec

val make_neg_binary_operator_fun :
  brand_model -> QcertOps.Binary.op -> provenance -> qcert_type ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  (provenance * qcert_type, provenance, absolute_name) ergo_expr ->
  ergoct_expr

val make_neg_binary_operator :
  brand_model -> binary_op -> binary_dispatch_spec

val binary_operator_dispatch_table :
  brand_model -> ergo_binary_operator -> binary_dispatch_table

val try_binary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
  binary_dispatch_table -> ergoct_expr -> ergoct_expr -> ergoct_expr eresult

val binary_dispatch :
  brand_model -> namespace_ctxt -> provenance -> ergo_binary_operator ->
  ergoct_expr -> ergoct_expr -> ergoct_expr eresult

val ergoc_expr_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_expr -> ergoct_expr
  eresult

val ergoc_function_typecheck :
  brand_model -> namespace_ctxt -> char list -> type_context ->
  ergoc_function -> (ergoct_function * type_context) eresult

val ergoc_clause_typecheck :
  brand_model -> namespace_ctxt -> type_context ->
  (char list * ergoc_function) ->
  ((char list * ergoct_function) * type_context) eresult

val ergoc_contract_typecheck :
  brand_model -> namespace_ctxt -> type_context -> absolute_name ->
  ergoc_contract -> (ergoct_contract * type_context) eresult

val ergoc_decl_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_declaration ->
  (ergoct_declaration * type_context) eresult

val ergoc_module_typecheck :
  brand_model -> namespace_ctxt -> type_context -> ergoc_module ->
  (ergoct_module * type_context) eresult

val mkResult :
  provenance -> (provenance, provenance, absolute_name) ergo_expr ->
  (provenance, provenance, absolute_name) ergo_expr -> (provenance,
  provenance, absolute_name) ergo_expr -> ergoc_expr

val setState :
  provenance -> (provenance, provenance, absolute_name) ergo_expr ->
  (provenance, provenance, absolute_name) ergo_expr -> ergoc_expr

val thisThis : provenance -> ergoc_expr

val setStateDot :
  provenance -> char list -> brand -> (provenance, provenance, char list)
  ergo_expr -> (provenance, provenance, absolute_name) ergo_expr -> ergoc_expr

val thisContract : provenance -> ergoc_expr

val thisClause : provenance -> char list -> ergoc_expr

val thisState : provenance -> ergoc_expr

val pushEmit :
  provenance -> (provenance, provenance, char list) ergo_expr -> (provenance,
  provenance, char list) ergo_expr -> ergoc_expr

val eSuccess : provenance -> ergoc_expr -> ergoc_expr

val eFailure : provenance -> ergoc_expr -> ergoc_expr

val eCallClause :
  provenance -> char list -> char list -> ergoc_expr list -> ergoc_expr

val eReturn : provenance -> ergoc_expr -> ergoc_expr

val eBindThis :
  provenance -> char list -> ergoc_expr -> (provenance, provenance,
  absolute_name) ergo_expr

val eWrapTop :
  provenance -> ergoc_expr -> (provenance, provenance, char list) ergo_expr

val eClauseAsFunction :
  provenance -> char list -> laergo_type -> laergo_type option -> laergo_type
  option -> laergo_type option -> (char list * (provenance, absolute_name)
  ergo_type) list -> ergoc_expr option -> char list * ergoc_function

val create_call :
  provenance -> char list -> char list -> char list -> ergoc_expr ->
  ergoc_expr list -> (char list * laergo_type) list -> ergoc_expr eresult

val case_of_sig :
  provenance -> char list -> char list -> ergoc_expr -> ergoc_expr list ->
  (char list * sigc) -> (absolute_name * ((provenance, absolute_name)
  ergo_pattern * ergoc_expr)) list eresult

val make_cases :
  laergo_type_declaration list -> provenance ->
  (absolute_name * (laergo_pattern * ergoc_expr)) list ->
  (laergo_pattern * ergoc_expr) list eresult

val match_of_sigs :
  laergo_type_declaration list -> provenance -> char list -> char list ->
  ergoc_expr -> ergoc_expr list -> (char list * sigc) list -> ergoc_expr
  eresult

val match_of_sigs_top :
  laergo_type_declaration list -> provenance -> char list -> ergoc_expr list
  -> (char list * sigc) list -> ergoc_expr eresult

val filter_init : (char list * sigc) list -> (char list * sigc) list

val create_main_clause_for_contract :
  laergo_type_declaration list -> provenance -> char list -> ergoc_contract
  -> (local_name * ergoc_function) eresult

val default_state : provenance -> ergoc_expr

val create_init_clause_for_contract :
  provenance -> ergoc_contract -> local_name * ergoc_function

val add_init_clause_to_contract : ergoc_contract -> ergoc_contract

val add_main_clause_to_contract :
  laergo_type_declaration list -> char list -> ergoc_contract ->
  ergoc_contract eresult

val ergoc_expand_declaration :
  laergo_type_declaration list -> ergoc_declaration -> ergoc_declaration
  eresult

val ergoc_expand_declarations :
  laergo_type_declaration list -> ergoc_declaration list -> ergoc_declaration
  list eresult

val ergoc_expand_module :
  laergo_type_declaration list -> ergoc_module -> ergoc_module eresult

val cto_type_to_ergo_type : lrcto_type -> lrergo_type

val cto_declaration_desc_to_ergo_type_declaration_desc :
  lrcto_declaration_desc -> lrergo_type_declaration_desc

val cto_declaration_to_ergo_type_declaration :
  lrcto_declaration -> lrergo_type_declaration

val cto_declaration_to_ergo_declaration :
  lrcto_declaration -> lrergo_declaration

val cto_import_to_ergo_declaration :
  provenance import_decl -> lrergo_declaration

val cto_package_to_ergo_module : lrcto_package -> lrergo_module

val toTextClause : provenance -> laergo_expr -> laergo_clause

val add_template_to_clauses :
  provenance -> laergo_expr -> laergo_clause list -> laergo_clause list

val add_template_to_contract :
  laergo_expr -> laergo_contract -> (provenance, provenance, absolute_name)
  ergo_contract

val add_template_to_declaration :
  laergo_expr -> laergo_declaration -> laergo_declaration

val add_template_to_module :
  laergo_expr -> laergo_module -> (provenance, provenance, absolute_name)
  ergo_module

val template_of_ergo_declaration :
  laergo_declaration -> (char list * char list) list

val template_of_ergo_declarations :
  laergo_declaration list -> (char list * char list) list

val template_of_ergo_module : laergo_module -> (char list * char list) list

val template_of_ergo_modules :
  laergo_module list -> (char list * char list) list

val find_template : provenance -> laergo_module list -> laergo_type eresult

val empty_main :
  provenance -> char list -> laergo_module list -> laergo_module eresult

val namespace_ctxt_of_ergo_decls :
  namespace_ctxt -> namespace_name -> lrergo_declaration list ->
  namespace_name * namespace_ctxt

val namespace_ctxt_of_ergo_module :
  namespace_ctxt -> lrergo_module -> namespace_ctxt

val namespace_ctxt_of_cto_packages :
  namespace_ctxt -> (provenance, relative_name) cto_package list ->
  namespace_ctxt

val lookup_one_import :
  namespace_ctxt -> limport_decl -> namespace_table eresult

val resolve_one_import :
  namespace_ctxt -> limport_decl -> namespace_ctxt eresult

val builtin_imports : char list list

val is_builtin_import : namespace_name -> bool

val stdlib_imports : char list list

val is_stdlib_import : namespace_name -> bool

val resolve_ergo_type : namespace_ctxt -> lrergo_type -> laergo_type eresult

val resolve_ergo_type_struct :
  namespace_ctxt -> (char list * lrergo_type) list ->
  (char list * laergo_type) list eresult

val resolve_type_annotation :
  provenance -> namespace_ctxt -> relative_name option -> absolute_name
  option eresult

val resolve_extends :
  provenance -> namespace_ctxt -> rextends -> aextends eresult

val resolve_ergo_type_signature :
  provenance -> namespace_ctxt -> char list -> lrergo_type_signature ->
  laergo_type_signature eresult

val resolve_ergo_type_clauses :
  provenance -> namespace_ctxt -> (char list * lrergo_type_signature) list ->
  (char list * laergo_type_signature) list eresult

val resolve_ergo_type_declaration_desc :
  provenance -> namespace_ctxt -> char list -> lrergo_type_declaration_desc
  -> laergo_type_declaration_desc eresult

val resolve_ergo_type_declaration :
  provenance -> namespace_name -> namespace_ctxt ->
  (abstract_ctxt * lrergo_type_declaration) ->
  ((abstract_ctxt * laergo_declaration) * ((char list * laergo_expr) * data)
  list) eresult

val resolve_ergo_pattern :
  namespace_ctxt -> lrergo_pattern -> laergo_pattern eresult

val resolve_ergo_expr : namespace_ctxt -> lrergo_expr -> laergo_expr eresult

val resolve_ergo_stmt : namespace_ctxt -> lrergo_stmt -> laergo_stmt eresult

val resolve_ergo_function :
  namespace_name -> namespace_ctxt -> char list -> lrergo_function ->
  laergo_function eresult

val resolve_ergo_clause :
  namespace_name -> namespace_ctxt -> (provenance, provenance, relative_name)
  ergo_clause -> laergo_clause eresult

val resolve_ergo_clauses :
  namespace_name -> namespace_ctxt -> (provenance, provenance, relative_name)
  ergo_clause list -> laergo_clause list eresult

val resolve_ergo_contract :
  namespace_name -> namespace_ctxt -> lrergo_contract -> laergo_contract
  eresult

val resolve_ergo_declaration :
  namespace_ctxt -> lrergo_declaration -> (laergo_declaration
  list * namespace_ctxt) eresult

val resolve_ergo_template_expr :
  namespace_ctxt -> lrergo_expr -> laergo_expr eresult

val resolve_ergo_declarations :
  namespace_ctxt -> lrergo_declaration list -> ((provenance, provenance,
  absolute_name) ergo_declaration list * namespace_ctxt) eresult

val silently_resolve_ergo_declarations :
  namespace_ctxt -> lrergo_declaration list -> namespace_ctxt eresult

val init_namespace_ctxt : namespace_ctxt

val patch_cto_imports :
  namespace_name -> lrergo_declaration list -> lrergo_declaration list

val patch_ergo_imports :
  namespace_name -> lrergo_declaration list -> lrergo_declaration list

val new_ergo_module_namespace :
  namespace_ctxt -> namespace_name -> namespace_ctxt eresult

val resolve_cto_package :
  namespace_ctxt -> lrcto_package -> (laergo_module * namespace_ctxt) eresult

val resolve_ergo_module :
  namespace_ctxt -> lrergo_module -> (laergo_module * namespace_ctxt) eresult

val resolve_ergo_template :
  namespace_ctxt -> (char list * lrergo_expr) option ->
  (char list * laergo_expr) option eresult

val resolve_ergo_modules :
  namespace_ctxt -> lrergo_module list -> (laergo_module
  list * namespace_ctxt) eresult

val resolve_cto_packages :
  namespace_ctxt -> lrcto_package list -> (laergo_module
  list * namespace_ctxt) eresult

val triage_ctos_and_ergos :
  lrergo_input list -> (lrcto_package list * lrergo_module
  list) * lrergo_module option

val empty_sigc : char list list -> provenance -> sigc

val mk_naked_closure :
  char list list -> ergoc_expr -> provenance -> ergoc_function

val mk_unary : QcertOps.Unary.op -> provenance -> ergoc_function

val mk_binary_expr0 : ergoc_expr -> provenance -> ergoc_function

val mk_binary : QcertOps.Binary.op -> provenance -> ergoc_function

type ergo_stdlib_table = (char list * (provenance -> ergoc_function)) list

val backend_compose_table :
  ergo_stdlib_table -> ergo_stdlib_table -> ergo_stdlib_table

val foreign_unary_operator_table : ergo_stdlib_table

val foreign_binary_operator_table : ergo_stdlib_table

val foreign_table : ergo_stdlib_table

val unary_operator_table : ergo_stdlib_table

val binary_operator_table : ergo_stdlib_table

val builtin_table : ergo_stdlib_table

val ergoc_stdlib : ergo_stdlib_table

type function_group_env = (char list * (char list * ergoc_function) list) list

type compilation_context = { compilation_context_namespace : namespace_ctxt;
                             compilation_context_function_env : (char list * ergoc_function)
                                                                list;
                             compilation_context_function_group_env : 
                             function_group_env;
                             compilation_context_global_env : (char list * ergoc_expr)
                                                              list;
                             compilation_context_local_env : (char list * ergoc_expr)
                                                             list;
                             compilation_context_params_env : char list list;
                             compilation_context_current_contract : char list
                                                                    option;
                             compilation_context_current_clause : char list
                                                                  option;
                             compilation_context_type_ctxt : type_context;
                             compilation_context_type_decls : laergo_type_declaration
                                                              list;
                             compilation_context_new_type_decls : laergo_type_declaration
                                                                  list;
                             compilation_context_warnings : ewarning list;
                             compilation_context_state_type : laergo_type
                                                              option }

val compilation_context_namespace :
  brand_model -> compilation_context -> namespace_ctxt

val compilation_context_function_env :
  brand_model -> compilation_context -> (char list * ergoc_function) list

val compilation_context_function_group_env :
  brand_model -> compilation_context -> function_group_env

val compilation_context_global_env :
  brand_model -> compilation_context -> (char list * ergoc_expr) list

val compilation_context_local_env :
  brand_model -> compilation_context -> (char list * ergoc_expr) list

val compilation_context_params_env :
  brand_model -> compilation_context -> char list list

val compilation_context_current_contract :
  brand_model -> compilation_context -> char list option

val compilation_context_current_clause :
  brand_model -> compilation_context -> char list option

val compilation_context_type_ctxt :
  brand_model -> compilation_context -> type_context

val compilation_context_type_decls :
  brand_model -> compilation_context -> laergo_type_declaration list

val compilation_context_new_type_decls :
  brand_model -> compilation_context -> laergo_type_declaration list

val compilation_context_warnings :
  brand_model -> compilation_context -> ewarning list

val compilation_context_state_type :
  brand_model -> compilation_context -> laergo_type option

val namespace_ctxt_of_compilation_context :
  brand_model -> compilation_context -> namespace_ctxt

val compilation_context_update_namespace :
  brand_model -> compilation_context -> namespace_ctxt -> compilation_context

val compilation_context_update_function_env :
  brand_model -> compilation_context -> char list -> ergoc_function ->
  compilation_context

val update_function_group_env :
  char list -> char list -> ergoc_function -> function_group_env ->
  function_group_env

val compilation_context_update_function_group_env :
  brand_model -> compilation_context -> char list -> char list ->
  ergoc_function -> compilation_context

val compilation_context_update_global_env :
  brand_model -> compilation_context -> char list -> ergoc_expr ->
  compilation_context

val compilation_context_update_local_env :
  brand_model -> compilation_context -> char list -> ergoc_expr ->
  compilation_context

val compilation_context_set_params_env :
  brand_model -> compilation_context -> char list list -> compilation_context

val set_namespace_in_compilation_context :
  brand_model -> namespace_name -> compilation_context -> compilation_context
  eresult

val set_current_contract :
  brand_model -> compilation_context -> char list -> laergo_type option ->
  compilation_context

val set_current_clause :
  brand_model -> compilation_context -> char list -> compilation_context

val compilation_context_update_type_ctxt :
  brand_model -> compilation_context -> type_context -> compilation_context

val compilation_context_update_type_declarations :
  brand_model -> compilation_context -> laergo_type_declaration list ->
  laergo_type_declaration list -> compilation_context

val compilation_context_add_new_type_declaration :
  brand_model -> compilation_context -> laergo_type_declaration ->
  compilation_context

val compilation_context_add_warnings :
  brand_model -> compilation_context -> ewarning list -> compilation_context

val compilation_context_reset_warnings :
  brand_model -> compilation_context -> compilation_context

val get_all_decls :
  brand_model -> compilation_context -> laergo_type_declaration list

val init_compilation_context :
  brand_model -> namespace_ctxt -> laergo_type_declaration list ->
  compilation_context

val is_abstract_class :
  brand_model -> compilation_context -> char list -> bool

val is_state_type_branded :
  brand_model -> compilation_context -> char list option

val ergo_expr_to_ergoc_expr :
  brand_model -> compilation_context -> laergo_expr -> ergoc_expr eresult

val ergo_stmt_to_expr :
  brand_model -> compilation_context -> laergo_stmt -> ergoc_expr eresult

val clause_to_calculus :
  brand_model -> compilation_context -> laergo_type -> laergo_type option ->
  laergo_clause -> (local_name * ergoc_function) eresult

val function_to_calculus :
  brand_model -> compilation_context -> laergo_function -> ergoc_function
  eresult

val contract_to_calculus :
  brand_model -> compilation_context -> laergo_contract -> ergoc_contract
  eresult

val ergo_stmt_to_expr_top :
  brand_model -> compilation_context -> provenance -> (provenance,
  provenance, absolute_name) ergo_stmt -> ergoc_expr eresult

val declaration_to_calculus :
  brand_model -> compilation_context -> laergo_declaration ->
  (ergoc_declaration list * compilation_context) eresult

val declarations_calculus :
  brand_model -> compilation_context -> (provenance, provenance,
  absolute_name) ergo_declaration list -> (ergoc_declaration
  list * compilation_context) eresult

val ergo_module_to_calculus :
  brand_model -> compilation_context -> laergo_module ->
  (ergoc_module * compilation_context) eresult

val ergo_map_expr :
  ('a4 -> char list -> ('a1, 'a2, 'a3) ergo_expr -> 'a4) -> ('a4 -> ('a1,
  'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult option) -> 'a4 ->
  ('a1, 'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult

type ergo_expr0 = laergo_expr

val ergo_map_expr_sane :
  brand_model -> compilation_context -> (compilation_context -> (provenance,
  provenance, absolute_name) ergo_expr -> (provenance, provenance,
  absolute_name) ergo_expr eresult option) -> (provenance, provenance,
  absolute_name) ergo_expr -> (provenance, provenance, absolute_name)
  ergo_expr eresult

val ergo_letify_function' :
  provenance -> ergo_expr0 -> ((char list * laergo_type option) * ergo_expr0)
  list -> ergo_expr0

val keep_param_types :
  (char list * laergo_type) list -> (char list * laergo_type option) list

val discard_param_types :
  (char list * laergo_type) list -> (char list * laergo_type option) list

val ergo_letify_function :
  provenance -> char list -> ergoc_function -> ergo_expr0 list -> ergo_expr0
  eresult

val ergo_inline_functions' :
  brand_model -> compilation_context -> ergo_expr0 -> ergo_expr0 eresult
  option

val ergo_inline_functions :
  brand_model -> compilation_context -> (provenance, provenance,
  absolute_name) ergo_expr -> (provenance, provenance, absolute_name)
  ergo_expr eresult

val ergo_inline_globals' :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult
  option

val ergo_inline_globals :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult

val ergo_inline_expr :
  brand_model -> compilation_context -> ergoc_expr -> ergoc_expr eresult

val ergo_inline_function :
  brand_model -> compilation_context -> ergoc_function -> ergoc_function
  eresult

val ergoc_inline_clause :
  brand_model -> char list -> compilation_context ->
  (char list * ergoc_function) ->
  ((char list * ergoc_function) * compilation_context) eresult

val ergo_inline_contract :
  brand_model -> char list -> compilation_context -> ergoc_contract ->
  (ergoc_contract * compilation_context) eresult

val ergoc_inline_declaration :
  brand_model -> compilation_context -> ergoc_declaration ->
  (ergoc_declaration * compilation_context) eresult

val ergoc_inline_declarations :
  brand_model -> compilation_context -> ergoc_declaration list ->
  (ergoc_declaration list * compilation_context) eresult

val ergoc_inline_module :
  brand_model -> compilation_context -> ergoc_module ->
  (ergoc_module * compilation_context) eresult

val fresh_in_match :
  ('a1 * ergo_nnrc_expr) list -> ergo_nnrc_expr -> char list

val fresh_in_case : ergo_nnrc_expr -> ergo_nnrc_expr -> char list

val new_array : ergo_nnrc_expr list -> ergo_nnrc_expr

val new_expr : char list -> ergo_nnrc_expr -> ergo_nnrc_expr

val ergo_pattern_to_nnrc :
  brand_model -> char list list -> ergo_nnrc_expr -> tlaergo_pattern ->
  char list list * ergo_nnrc_expr

val pack_pattern :
  char list list -> ergo_nnrc_expr -> ergo_nnrc_expr -> ergo_nnrc_expr ->
  ergo_nnrc_expr

val ergoct_expr_to_nnrc :
  brand_model -> char list list -> ergoct_expr -> ergo_nnrc_expr eresult

val functionct_to_nnrc :
  brand_model -> absolute_name -> ergoct_function ->
  (char list * ergo_nnrc_lambda) eresult

val clausect_declaration_to_nnrc :
  brand_model -> absolute_name -> ergoct_function ->
  (char list * ergo_nnrc_lambda) eresult

val contractct_to_nnrc :
  brand_model -> ergoct_contract -> ergo_nnrc_function_table eresult

val declarationct_to_nnrc :
  brand_model -> ergoct_declaration -> ergo_nnrc_declaration list eresult

val declarationsct_calculus_with_table :
  brand_model -> ergoct_declaration list -> ergo_nnrc_declaration list eresult

val modulect_to_nnrc_with_table :
  brand_model -> ergoct_module -> ergo_nnrc_module eresult

val ergoct_module_to_nnrc :
  brand_model -> ergoct_module -> ergo_nnrc_module eresult

type ergo_imp_lambda = QcertCodeGen.imp_ejson_function

type ergo_imp_function_table = QcertCodeGen.imp_ejson_lib

type ergo_imp_declaration =
| DIFunc of char list * ergo_imp_lambda
| DIFuncTable of char list * ergo_imp_function_table

type ergo_imp_module = { modulei_provenance : provenance;
                         modulei_namespace : char list;
                         modulei_declarations : ergo_imp_declaration list }

val modulei_namespace : ergo_imp_module -> char list

val modulei_declarations : ergo_imp_module -> ergo_imp_declaration list

val ergo_nnrc_function_to_imp :
  brand_model -> char list list -> ergo_nnrc_lambda -> ergo_imp_lambda

val ergo_nnrc_function_table_to_imp :
  brand_model -> char list list -> ergo_nnrc_function_table ->
  ergo_imp_function_table

val ergo_nnrc_declaration_to_imp :
  brand_model -> char list list -> ergo_nnrc_declaration ->
  ergo_imp_declaration

val ergo_nnrc_declarations_to_imp :
  brand_model -> ergo_nnrc_declaration list -> ergo_imp_declaration list

val ergo_nnrc_module_to_imp :
  brand_model -> ergo_nnrc_module -> ergo_imp_module

val accord_annotation :
  bool -> char list -> char list -> char list -> char list -> char list ->
  nstring -> nstring -> nstring

val ergo_imp_function_to_javascript_ast :
  brand_model -> char list -> ergo_imp_lambda -> char list option -> js_ast

val ergo_imp_function_table_to_javascript_ast :
  brand_model -> char list -> ergo_imp_function_table -> js_ast

val preamble : js_ast

val postamble : js_ast

val ergo_imp_declaration_to_javascript_ast :
  brand_model -> ergo_imp_declaration -> js_ast

val ergo_imp_declarations_to_javascript_ast :
  brand_model -> ergo_imp_declaration list -> js_ast

val ergo_imp_module_to_javascript_ast :
  brand_model -> ergo_imp_module -> js_ast

val ergo_imp_module_to_javascript_top :
  brand_model -> (char list * char list) list -> ergo_imp_module ->
  QcertCodeGen.ejavascript

val wrapper_function_for_clause :
  bool -> char list -> char list -> char list -> char list -> char list ->
  char list -> char list -> char list -> nstring -> nstring -> nstring

val wrapper_function_for_init :
  bool -> char list -> char list -> char list -> char list -> char list ->
  nstring -> nstring -> nstring

val apply_wrapper_function :
  char list -> char list ->
  ((((char list * char list) * char list) * char list) * char list) ->
  nstring -> nstring -> nstring

val wrapper_functions :
  char list ->
  (((((char list * char list) * char list) * char list) * char list)
  list * char list) -> nstring -> nstring -> nstring

val javascript_main_dispatch_and_init :
  char list -> nstring -> nstring -> nstring

val javascript_of_module_with_dispatch :
  brand_model -> char list ->
  (((((char list * char list) * char list) * char list) * char list)
  list * char list) -> ergo_imp_module -> nstring -> nstring -> nstring

val filter_signatures :
  char list -> (char list * laergo_type_signature) list ->
  ((((char list * char list) * char list) * char list) * char list) list

val filter_signatures_with_state :
  char list -> laergo_type option -> (char list * (provenance, absolute_name)
  ergo_type_signature) list ->
  ((((char list * char list) * char list) * char list) * char list)
  list * char list

val ergo_imp_module_to_es6 :
  brand_model -> char list -> (provenance, absolute_name) ergo_type option ->
  (char list * (provenance, absolute_name) ergo_type_signature) list ->
  ergo_imp_module -> QcertCodeGen.ejavascript

val java_method_of_body :
  ergo_nnrc_expr -> char list -> nstring -> nstring -> QcertCodeGen.java

val java_method_of_nnrc_function :
  brand_model -> char list -> ergo_nnrc_lambda -> nstring -> nstring ->
  QcertCodeGen.java

val java_methods_of_nnrc_functions :
  brand_model -> (char list * ergo_nnrc_lambda) list -> char list -> nstring
  -> nstring -> QcertCodeGen.java

val java_class_of_nnrc_function_table :
  brand_model -> char list -> ergo_nnrc_function_table -> nstring -> nstring
  -> QcertCodeGen.java

val preamble0 : nstring -> nstring

val java_of_declaration :
  brand_model -> char list -> ergo_nnrc_declaration -> int -> int -> nstring
  -> nstring -> (QcertCodeGen.java * QcertCodeGen.java_data) * int

val java_of_declarations :
  brand_model -> char list -> ergo_nnrc_declaration list -> int -> int ->
  nstring -> nstring -> QcertCodeGen.java

val nnrc_module_to_java :
  brand_model -> char list -> ergo_nnrc_module -> nstring -> nstring ->
  QcertCodeGen.java

val nnrc_module_to_java_top :
  brand_model -> char list -> ergo_nnrc_module -> QcertCodeGen.java

val resolve_inputs_opt :
  lrergo_input list -> (char list * lrergo_expr) option -> ((laergo_module
  list * laergo_module option) * namespace_ctxt) eresult

val resolve_inputs :
  lrergo_input list -> (char list * lrergo_expr) option -> ((laergo_module
  list * laergo_module) * namespace_ctxt) eresult

val resolve_inputs_no_main :
  lrergo_input list -> (char list * lrergo_expr) option -> (laergo_module
  list * namespace_ctxt) eresult

val just_resolved_inputs :
  lrergo_input list -> (char list * lrergo_expr) option -> laergo_module list
  eresult

val brand_model_from_inputs :
  lrergo_input list -> (QcertType.tbrand_model * laergo_type_declaration
  list) eresult

val init_compilation_context_from_inputs :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) option ->
  laergo_type_declaration list -> ((laergo_module
  list * laergo_module) * compilation_context) eresult

val init_compilation_context_from_inputs_no_main :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) option ->
  laergo_type_declaration list -> (laergo_module list * compilation_context)
  eresult

val ergo_module_to_ergoct :
  brand_model -> compilation_context -> laergo_module ->
  (ergoct_module * compilation_context) eresult

val ergo_modules_to_ergoct :
  brand_model -> compilation_context -> laergo_module list -> (ergoct_module
  list * compilation_context) eresult

val ergo_declaration_to_ergoc :
  brand_model -> compilation_context -> lrergo_declaration ->
  (ergoc_declaration list * compilation_context) eresult

val ergo_declaration_to_ergoct_inlined :
  brand_model -> compilation_context -> lrergo_declaration ->
  (ergoct_declaration list * compilation_context) eresult

val compilation_context_from_inputs :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) option ->
  laergo_type_declaration list -> (laergo_module * compilation_context)
  eresult

val compilation_context_from_inputs_no_main :
  brand_model -> lrergo_input list -> (char list * lrergo_expr) option ->
  laergo_type_declaration list -> compilation_context eresult

val ergo_module_to_java :
  brand_model -> compilation_context -> laergo_module ->
  (ergo_nnrc_module * QcertCodeGen.java) eresult

val ergo_module_to_java_top :
  lrergo_input list -> (char list * lrergo_expr) option -> result_file eresult

val ergoc_module_to_es6 :
  brand_model -> char list -> (provenance, absolute_name) ergo_type option ->
  (char list * (provenance, absolute_name) ergo_type_signature) list ->
  ergo_nnrc_module -> QcertCodeGen.ejavascript

val ergo_module_to_es6_top :
  lrergo_input list -> (char list * lrergo_expr) option -> result_file eresult

type repl_context = { repl_context_eval_ctxt : eval_context;
                      repl_context_comp_ctxt : compilation_context }

val repl_context_eval_ctxt : brand_model -> repl_context -> eval_context

val repl_context_comp_ctxt :
  brand_model -> repl_context -> compilation_context

val init_repl_context :
  brand_model -> lrergo_input list -> repl_context eresult

val update_repl_ctxt_comp_ctxt :
  brand_model -> repl_context -> compilation_context -> repl_context

val update_repl_ctxt_type_ctxt :
  brand_model -> repl_context -> type_context -> repl_context

val update_repl_ctxt_eval_ctxt :
  brand_model -> repl_context -> eval_context -> repl_context

val lift_repl_ctxt :
  brand_model -> repl_context -> ((qcert_type option * qcert_data
  option) * repl_context) eresult -> repl_context

val ergoc_repl_eval_declaration :
  brand_model -> repl_context -> ergoct_declaration -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergoct_repl_eval_declarations :
  brand_model -> repl_context -> ergoct_declaration list -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergoct_eval_decl_via_calculus :
  brand_model -> repl_context -> lrergo_declaration -> ((qcert_type
  option * qcert_data option) * repl_context) eresult

val ergo_string_of_result :
  brand_model -> repl_context -> ((qcert_type option * qcert_data
  option) * repl_context) eresult -> char list eresult

val ergoct_repl_eval_decl :
  brand_model -> repl_context -> lrergo_declaration -> char list
  eresult * repl_context

val refresh_brand_model_in_comp_ctxt :
  brand_model -> compilation_context ->
  (QcertType.tbrand_model * compilation_context) eresult

val refresh_brand_model :
  brand_model -> repl_context -> (QcertType.tbrand_model * repl_context)
  eresult

module ErgoCompiler :
 sig
  val ergo_version : char list

  module ErgoData :
   sig
    type json = Coq__3.json

    type data = Coq__4.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : Coq__3.json list -> json

    val jobject : (char list * Coq__3.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Coq__4.data list -> data

    val drec : (char list * Coq__4.data) list -> data

    val dleft : data -> data

    val dright : data -> data

    val dbrand : brands -> data -> data

    val dsome : data -> data

    val dnone : data

    val dsuccess : data -> data

    val derror : data -> data
   end

  module ErgoOps :
   sig
    module ErgoData :
     sig
      type json = Coq__3.json

      type data = Coq__4.data

      type t = data

      val jnull : json

      val jnumber : float -> json

      val jbool : bool -> json

      val jstring : char list -> json

      val jarray : Coq__3.json list -> json

      val jobject : (char list * Coq__3.json) list -> json

      val dunit : data

      val dnat : int -> data

      val dfloat : float -> data

      val dbool : bool -> data

      val dstring : char list -> data

      val dcoll : Coq__4.data list -> data

      val drec : (char list * Coq__4.data) list -> data

      val dleft : data -> data

      val dright : data -> data

      val dbrand : brands -> data -> data

      val dsome : data -> data

      val dnone : data

      val dsuccess : data -> data

      val derror : data -> data
     end

    module Unary :
     sig
      type op = unary_op

      type t = op

      module Double :
       sig
        val opuminus : op

        val opabs : op

        val oplog2 : op

        val opsqrt : op

        val opsum : op

        val opnummin : op

        val opnummax : op

        val opnummean : op
       end

      val opidentity : op

      val opneg : op

      val oprec : char list -> op

      val opdot : char list -> op

      val oprecremove : char list -> op

      val oprecproject : char list list -> op

      val opbag : op

      val opsingleton : op

      val opflatten : op

      val opdistinct : op

      val opcount : op

      val optostring : op

      val opsubstring : int -> int option -> op

      val oplike : char list -> op

      val opleft : op

      val opright : op

      val opbrand : brands -> op

      val opunbrand : op

      val opcast : brands -> op

      val eval :
        brand_relation_t -> unary_op -> ErgoData.data -> ErgoData.data option
     end

    module Binary :
     sig
      type op = binary_op

      type t = op

      module Double :
       sig
        val opplus : op

        val opminus : op

        val opmult : op

        val opmin : op

        val opmax : op

        val opdiv : op

        val oppow : op

        val oplt : op

        val ople : op

        val opgt : op

        val opge : op
       end

      module Integer :
       sig
        val opplusi : op

        val opminusi : op

        val opmulti : op

        val opdivi : op

        val oplti : op

        val oplei : op
       end

      module DateTime :
       sig
        val opdateadd : op

        val opdatesubtract : op

        val opdateisbefore : op

        val opdateisafter : op

        val opdatediff : op
       end

      val opequal : op

      val oprecconcat : op

      val oprecmerge : op

      val opand : op

      val opor : op

      val opbagunion : op

      val opbagdiff : op

      val opbagmin : op

      val opbagmax : op

      val opnth : op

      val opcontains : op

      val opstringconcat : op

      val opstringjoin : op

      val eval :
        brand_relation_t -> binary_op -> ErgoData.data -> ErgoData.data ->
        ErgoData.data option
     end
   end

  module ErgoCType :
   sig
    val empty_brand_model : unit -> brand_model

    type record_kind = Coq__2.record_kind

    val open_kind : record_kind

    val closed_kind : record_kind

    type qtype_struct = rtype_UU2080_

    type qtype = rtype

    type t = qtype

    val tbottom : brand_relation -> qtype

    val ttop : brand_relation -> qtype

    val tunit : brand_relation -> qtype

    val tfloat : brand_relation -> qtype

    val tnat : brand_relation -> qtype

    val tbool : brand_relation -> qtype

    val tstring : brand_relation -> qtype

    val tdateTimeFormat : brand_relation -> qtype

    val tdateTime : brand_relation -> qtype

    val tduration : brand_relation -> qtype

    val tperiod : brand_relation -> qtype

    val tcoll : brand_relation -> qtype -> qtype

    val trec :
      brand_relation -> record_kind -> (char list * qtype) list -> qtype

    val teither : brand_relation -> qtype -> qtype -> qtype

    val tarrow : brand_relation -> qtype -> qtype -> qtype

    val tbrand : brand_relation -> char list list -> qtype

    val toption : brand_relation -> qtype -> qtype

    val qcert_type_meet : brand_relation -> qtype -> qtype -> qtype

    val qcert_type_join : brand_relation -> qtype -> qtype -> qtype

    val qcert_type_subtype_dec : brand_model -> qtype -> qtype -> bool

    val untcoll : brand_model -> qtype -> qtype option

    val unteither : brand_model -> qtype -> (qtype * qtype) option

    val untrec :
      brand_model -> qtype -> (record_kind * (char list * qtype) list) option

    val qcert_type_infer_data : brand_model -> data -> qtype option

    val qcert_type_infer_binary_op :
      brand_model -> binary_op -> qtype -> qtype -> ((qtype * qtype) * qtype)
      option

    val qcert_type_infer_unary_op :
      brand_model -> unary_op -> qtype -> (qtype * qtype) option

    val unpack_qcert_type : brand_relation -> qtype -> qtype_struct

    type tbrand_relation = brand_relation

    val tempty_brand_relation : tbrand_relation

    val mk_tbrand_relation :
      (char list * char list) list -> tbrand_relation qresult

    type tbrand_context_decls = brand_context_decls

    type tbrand_context = brand_context

    val mk_tbrand_context :
      brand_relation -> tbrand_context_decls -> tbrand_context

    type tbrand_model = brand_model

    val mk_tbrand_model :
      brand_relation -> tbrand_context_decls -> tbrand_model qresult

    val tempty_brand_model : tbrand_model

    val qcert_type_unpack : brand_relation -> qtype -> qtype_struct

    val qcert_type_closed_from_open : brand_model -> qtype -> qtype

    val infer_brand_strict :
      brand_model -> brands -> qtype -> (rtype * qtype) option

    val recminus :
      brand_relation -> (char list * rtype) list -> char list list ->
      (char list * rtype) list

    val diff_record_types :
      brand_model -> brands -> qtype -> (char list list * char list list)
      option

    val rec_fields_that_are_not_subtype :
      brand_model -> (char list * qtype) list -> (char list * qtype) list ->
      ((char list * qtype) * qtype) list

    val fields_that_are_not_subtype :
      brand_model -> brands -> qtype -> ((char list * qtype) * qtype) list
   end

  val javascript_identifier_sanitizer : char list -> char list

  type location = Coq__6.location

  type provenance = Coq__7.provenance

  val loc_of_provenance : Coq__7.provenance -> Coq__6.location

  val prov_func : Coq__6.location -> char list -> Coq__7.provenance

  val prov_clause : Coq__6.location -> char list -> Coq__7.provenance

  val prov_this_contract : Coq__6.location -> Coq__7.provenance

  val prov_this_clause : Coq__6.location -> Coq__7.provenance

  val prov_this_state : Coq__6.location -> Coq__7.provenance

  val prov_loc : Coq__6.location -> Coq__7.provenance

  type relative_name = Coq__8.relative_name

  val this_name : char list

  type eerror = Coq__9.eerror

  type ewarning = Coq__10.ewarning

  val system_error : provenance -> char list -> eerror

  val parse_error : provenance -> char list -> eerror

  val compilation_error : provenance -> char list -> eerror

  val type_error : provenance -> char list -> eerror

  val runtime_error : provenance -> char list -> eerror

  type 'a eresult = 'a Coq__11.eresult

  val esuccess : 'a1 -> ewarning list -> 'a1 eresult

  val efailure : eerror -> 'a1 eresult

  type result_file = Coq__12.result_file

  type cto_type = lrcto_type

  type cto_declaration_desc = lrcto_declaration_desc

  type cto_declaration = lrcto_declaration

  type cto_package = lrcto_package

  val cto_boolean : provenance -> cto_type

  val cto_string : provenance -> cto_type

  val cto_double : provenance -> cto_type

  val cto_long : provenance -> cto_type

  val cto_integer : provenance -> cto_type

  val cto_dateTime : provenance -> cto_type

  val cto_class_ref : Coq__7.provenance -> Coq__8.relative_name -> cto_type

  val cto_option :
    Coq__7.provenance -> (Coq__7.provenance, Coq__8.relative_name)
    Coq__13.cto_type -> cto_type

  val cto_array :
    Coq__7.provenance -> (Coq__7.provenance, Coq__8.relative_name)
    Coq__13.cto_type -> cto_type

  val cto_enum : char list list -> cto_declaration_desc

  val cto_transaction :
    bool -> relative_name option -> (char list * cto_type) list ->
    cto_declaration_desc

  val cto_concept :
    bool -> relative_name option -> (char list * cto_type) list ->
    cto_declaration_desc

  val mk_cto_declaration :
    Coq__7.provenance -> char list -> cto_declaration_desc -> cto_declaration

  val mk_cto_package :
    Coq__7.provenance -> char list -> char list -> char list ->
    Coq__7.provenance import_decl list -> cto_declaration list -> cto_package

  type ergo_type = lrergo_type

  type ergo_type_declaration_desc = lrergo_type_declaration_desc

  type ergo_type_declaration = lrergo_type_declaration

  type laergo_type_declaration = Coq__14.laergo_type_declaration

  val ergo_type_any : Coq__7.provenance -> ergo_type

  val ergo_type_nothing : Coq__7.provenance -> ergo_type

  val ergo_type_unit : Coq__7.provenance -> ergo_type

  val ergo_type_boolean : Coq__7.provenance -> ergo_type

  val ergo_type_string : Coq__7.provenance -> ergo_type

  val ergo_type_double : Coq__7.provenance -> ergo_type

  val ergo_type_long : Coq__7.provenance -> ergo_type

  val ergo_type_integer : Coq__7.provenance -> ergo_type

  val ergo_type_dateTime_format : Coq__7.provenance -> ergo_type

  val ergo_type_dateTime : Coq__7.provenance -> ergo_type

  val ergo_type_duration : Coq__7.provenance -> ergo_type

  val ergo_type_period : Coq__7.provenance -> ergo_type

  val ergo_type_class_ref :
    Coq__7.provenance -> Coq__8.relative_name -> ergo_type

  val ergo_type_option :
    Coq__7.provenance -> (Coq__7.provenance, Coq__8.relative_name)
    Coq__15.ergo_type -> ergo_type

  val ergo_type_record :
    Coq__7.provenance -> (char list * (Coq__7.provenance,
    Coq__8.relative_name) Coq__15.ergo_type) list -> ergo_type

  val ergo_type_array :
    Coq__7.provenance -> (Coq__7.provenance, Coq__8.relative_name)
    Coq__15.ergo_type -> ergo_type

  val ergo_type_transaction :
    bool -> relative_name option -> (char list * ergo_type) list ->
    ergo_type_declaration_desc

  val ergo_type_concept :
    bool -> relative_name option -> (char list * ergo_type) list ->
    ergo_type_declaration_desc

  val mk_ergo_type_declaration :
    Coq__7.provenance -> char list -> ergo_type_declaration_desc ->
    ergo_type_declaration

  type ergo_expr = lrergo_expr

  type ergo_stmt = lrergo_stmt

  type ergo_function = lrergo_function

  type ergo_clause = lrergo_clause

  type ergo_declaration = lrergo_declaration

  type ergo_contract = lrergo_contract

  type ergo_module = lrergo_module

  type ergo_input = lrergo_input

  val ecasedata : Coq__7.provenance -> ErgoData.data -> lrergo_pattern

  val ecaseenum :
    Coq__7.provenance -> (char list option * char list) -> lrergo_pattern

  val ecasewildcard :
    Coq__7.provenance -> Coq__8.relative_name type_annotation ->
    lrergo_pattern

  val ecaselet :
    Coq__7.provenance -> char list -> Coq__8.relative_name type_annotation ->
    lrergo_pattern

  val ecaseletoption :
    Coq__7.provenance -> char list -> Coq__8.relative_name type_annotation ->
    lrergo_pattern

  val ethis_this : Coq__7.provenance -> ergo_expr

  val ethis_contract : Coq__7.provenance -> ergo_expr

  val ethis_clause : Coq__7.provenance -> ergo_expr

  val ethis_state : Coq__7.provenance -> ergo_expr

  val evar : Coq__7.provenance -> Coq__8.relative_name -> ergo_expr

  val econst : Coq__7.provenance -> data -> ergo_expr

  val enone : Coq__7.provenance -> ergo_expr

  val esome : Coq__7.provenance -> ergo_expr -> ergo_expr

  val earray :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr list -> ergo_expr

  val etext :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr list -> ergo_expr

  val eunaryoperator :
    Coq__7.provenance -> ergo_unary_operator -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr -> ergo_expr

  val ebinaryoperator :
    Coq__7.provenance -> ergo_binary_operator -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr -> ergo_expr

  val eunarybuiltin :
    Coq__7.provenance -> QcertOps.Unary.op -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr -> ergo_expr

  val ebinarybuiltin :
    Coq__7.provenance -> QcertOps.Binary.op -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr -> ergo_expr

  val eif :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr -> ergo_expr

  val elet :
    Coq__7.provenance -> char list -> (Coq__7.provenance,
    Coq__8.relative_name) Coq__15.ergo_type option -> ergo_expr -> ergo_expr
    -> ergo_expr

  val eprint : Coq__7.provenance -> ergo_expr -> ergo_expr -> ergo_expr

  val enew :
    Coq__7.provenance -> Coq__8.relative_name ->
    (char list * (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr) list -> ergo_expr

  val erecord :
    Coq__7.provenance -> (char list * (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr) list -> ergo_expr

  val ecallfun :
    Coq__7.provenance -> Coq__8.relative_name -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr list ->
    ergo_expr

  val ematch :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> ((Coq__7.provenance,
    Coq__8.relative_name) ergo_pattern * (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr) list ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr -> ergo_expr

  val eforeach :
    Coq__7.provenance -> (char list * (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr) list -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr option ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr -> ergo_expr

  val opuminusi :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> ergo_expr

  val sreturn :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> ergo_stmt

  val efunreturn : provenance -> ergo_expr -> ergo_expr

  val sthrow :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> ergo_stmt

  val scallclause :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> char list ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__16.ergo_expr list -> ergo_stmt

  val scallcontract : Coq__7.provenance -> ergo_expr -> ergo_expr -> ergo_stmt

  val ssetstate :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__17.ergo_stmt -> ergo_stmt

  val ssetstatedot :
    Coq__7.provenance -> char list -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__17.ergo_stmt -> ergo_stmt

  val semit :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__17.ergo_stmt -> ergo_stmt

  val slet :
    Coq__7.provenance -> char list -> (Coq__7.provenance,
    Coq__8.relative_name) Coq__15.ergo_type option -> ergo_expr -> ergo_stmt
    -> ergo_stmt

  val sprint : Coq__7.provenance -> ergo_expr -> ergo_stmt -> ergo_stmt

  val sif :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__17.ergo_stmt ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__17.ergo_stmt -> ergo_stmt

  val senforce :
    Coq__7.provenance -> ergo_expr -> ergo_stmt option -> ergo_stmt ->
    ergo_stmt

  val smatch :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__16.ergo_expr -> ((Coq__7.provenance,
    Coq__8.relative_name) ergo_pattern * (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__17.ergo_stmt) list ->
    (Coq__7.provenance, Coq__7.provenance, Coq__8.relative_name)
    Coq__17.ergo_stmt -> ergo_stmt

  val eoptionaldot : Coq__7.provenance -> char list -> ergo_expr -> ergo_expr

  val eoptionaldefault :
    Coq__7.provenance -> ergo_expr -> ergo_expr -> ergo_expr

  val sreturnempty : Coq__7.provenance -> ergo_stmt

  val efunreturnempty : Coq__7.provenance -> ergo_expr

  val dnamespace : Coq__7.provenance -> namespace_name -> ergo_declaration

  val dimport :
    Coq__7.provenance -> Coq__7.provenance import_decl -> ergo_declaration

  val dtype :
    Coq__7.provenance -> (Coq__7.provenance, Coq__8.relative_name)
    Coq__18.ergo_type_declaration -> ergo_declaration

  val dstmt :
    Coq__7.provenance -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__17.ergo_stmt -> ergo_declaration

  val dconstant :
    Coq__7.provenance -> local_name -> (Coq__7.provenance,
    Coq__8.relative_name) Coq__15.ergo_type option -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr ->
    ergo_declaration

  val dfunc :
    Coq__7.provenance -> local_name -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__19.ergo_function -> ergo_declaration

  val dcontract :
    Coq__7.provenance -> local_name -> (Coq__7.provenance, Coq__7.provenance,
    Coq__8.relative_name) Coq__20.ergo_contract -> ergo_declaration

  val dsetcontract :
    Coq__7.provenance -> Coq__8.relative_name -> (Coq__7.provenance,
    Coq__7.provenance, Coq__8.relative_name) Coq__16.ergo_expr ->
    ergo_declaration

  val ergo_module_to_es6 :
    ergo_input list -> (char list * ergo_expr) option -> result_file
    Coq__11.eresult

  val ergo_module_to_java :
    ergo_input list -> (char list * ergo_expr) option -> result_file
    Coq__11.eresult

  type ergo_brand_model = ErgoCType.tbrand_model

  val ergo_empty_brand_model : ErgoCType.tbrand_model

  val ergo_brand_model_from_inputs :
    ergo_input list -> (ergo_brand_model * laergo_type_declaration list)
    eresult

  val ergo_refresh_brand_model :
    ergo_brand_model -> repl_context -> (ergo_brand_model * repl_context)
    eresult

  val init_repl_context :
    ergo_brand_model -> ergo_input list -> repl_context Coq__11.eresult

  val ergo_repl_eval_decl :
    ergo_brand_model -> repl_context -> ergo_declaration -> char list
    Coq__11.eresult * repl_context
 end
