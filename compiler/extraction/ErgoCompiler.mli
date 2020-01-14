open Ast
open BinaryOperators
open BrandRelation
open CTO
open Data
open DataResult
open Ergo
open ErgoDriver
open ErgoSugar
open ErgoType
open JSON
open Names
open Provenance
open QLib
open RType
open Result0
open TBrandContext
open TBrandModel
open UnaryOperators
open Version

module ErgoCompiler :
 sig
  val ergo_version : char list

  module ErgoData :
   sig
    type json = JSON.json

    type data = Data.data

    type t = data

    val jnull : json

    val jnumber : float -> json

    val jbool : bool -> json

    val jstring : char list -> json

    val jarray : JSON.json list -> json

    val jobject : (char list * JSON.json) list -> json

    val dunit : data

    val dnat : int -> data

    val dfloat : float -> data

    val dbool : bool -> data

    val dstring : char list -> data

    val dcoll : Data.data list -> data

    val drec : (char list * Data.data) list -> data

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
      type json = JSON.json

      type data = Data.data

      type t = data

      val jnull : json

      val jnumber : float -> json

      val jbool : bool -> json

      val jstring : char list -> json

      val jarray : JSON.json list -> json

      val jobject : (char list * JSON.json) list -> json

      val dunit : data

      val dnat : int -> data

      val dfloat : float -> data

      val dbool : bool -> data

      val dstring : char list -> data

      val dcoll : Data.data list -> data

      val drec : (char list * Data.data) list -> data

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

    type record_kind = RType.record_kind

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

  type location = Provenance.location

  type provenance = Provenance.provenance

  val loc_of_provenance : Provenance.provenance -> Provenance.location

  val prov_func : Provenance.location -> char list -> Provenance.provenance

  val prov_clause : Provenance.location -> char list -> Provenance.provenance

  val prov_this_contract : Provenance.location -> Provenance.provenance

  val prov_this_clause : Provenance.location -> Provenance.provenance

  val prov_this_state : Provenance.location -> Provenance.provenance

  val prov_loc : Provenance.location -> Provenance.provenance

  type relative_name = Names.relative_name

  val this_name : char list

  type eerror = Result0.eerror

  type ewarning = Result0.ewarning

  val system_error : provenance -> char list -> eerror

  val parse_error : provenance -> char list -> eerror

  val compilation_error : provenance -> char list -> eerror

  val type_error : provenance -> char list -> eerror

  val runtime_error : provenance -> char list -> eerror

  type 'a eresult = 'a Result0.eresult

  val esuccess : 'a1 -> ewarning list -> 'a1 eresult

  val efailure : eerror -> 'a1 eresult

  type result_file = Result0.result_file

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

  val cto_class_ref : Provenance.provenance -> Names.relative_name -> cto_type

  val cto_option :
    Provenance.provenance -> (Provenance.provenance, Names.relative_name)
    CTO.cto_type -> cto_type

  val cto_array :
    Provenance.provenance -> (Provenance.provenance, Names.relative_name)
    CTO.cto_type -> cto_type

  val cto_enum : char list list -> cto_declaration_desc

  val cto_transaction :
    bool -> relative_name option -> (char list * cto_type) list ->
    cto_declaration_desc

  val cto_concept :
    bool -> relative_name option -> (char list * cto_type) list ->
    cto_declaration_desc

  val mk_cto_declaration :
    Provenance.provenance -> char list -> cto_declaration_desc ->
    cto_declaration

  val mk_cto_package :
    Provenance.provenance -> char list -> char list -> char list ->
    Provenance.provenance import_decl list -> cto_declaration list ->
    cto_package

  type ergo_type = lrergo_type

  type ergo_type_declaration_desc = lrergo_type_declaration_desc

  type ergo_type_declaration = lrergo_type_declaration

  type laergo_type_declaration = ErgoType.laergo_type_declaration

  val ergo_type_any : Provenance.provenance -> ergo_type

  val ergo_type_nothing : Provenance.provenance -> ergo_type

  val ergo_type_unit : Provenance.provenance -> ergo_type

  val ergo_type_boolean : Provenance.provenance -> ergo_type

  val ergo_type_string : Provenance.provenance -> ergo_type

  val ergo_type_double : Provenance.provenance -> ergo_type

  val ergo_type_long : Provenance.provenance -> ergo_type

  val ergo_type_integer : Provenance.provenance -> ergo_type

  val ergo_type_dateTime_format : Provenance.provenance -> ergo_type

  val ergo_type_dateTime : Provenance.provenance -> ergo_type

  val ergo_type_duration : Provenance.provenance -> ergo_type

  val ergo_type_period : Provenance.provenance -> ergo_type

  val ergo_type_class_ref :
    Provenance.provenance -> Names.relative_name -> ergo_type

  val ergo_type_option :
    Provenance.provenance -> (Provenance.provenance, Names.relative_name)
    ErgoType.ergo_type -> ergo_type

  val ergo_type_record :
    Provenance.provenance -> (char list * (Provenance.provenance,
    Names.relative_name) ErgoType.ergo_type) list -> ergo_type

  val ergo_type_array :
    Provenance.provenance -> (Provenance.provenance, Names.relative_name)
    ErgoType.ergo_type -> ergo_type

  val ergo_type_transaction :
    bool -> relative_name option -> (char list * ergo_type) list ->
    ergo_type_declaration_desc

  val ergo_type_concept :
    bool -> relative_name option -> (char list * ergo_type) list ->
    ergo_type_declaration_desc

  val mk_ergo_type_declaration :
    Provenance.provenance -> char list -> ergo_type_declaration_desc ->
    ergo_type_declaration

  type ergo_expr = lrergo_expr

  type ergo_stmt = lrergo_stmt

  type ergo_function = lrergo_function

  type ergo_clause = lrergo_clause

  type ergo_declaration = lrergo_declaration

  type ergo_contract = lrergo_contract

  type ergo_module = lrergo_module

  type ergo_input = lrergo_input

  val ecasedata : Provenance.provenance -> ErgoData.data -> lrergo_pattern

  val ecaseenum :
    Provenance.provenance -> (char list option * char list) -> lrergo_pattern

  val ecasewildcard :
    Provenance.provenance -> Names.relative_name type_annotation ->
    lrergo_pattern

  val ecaselet :
    Provenance.provenance -> char list -> Names.relative_name type_annotation
    -> lrergo_pattern

  val ecaseletoption :
    Provenance.provenance -> char list -> Names.relative_name type_annotation
    -> lrergo_pattern

  val ethis_this : Provenance.provenance -> ergo_expr

  val ethis_contract : Provenance.provenance -> ergo_expr

  val ethis_clause : Provenance.provenance -> ergo_expr

  val ethis_state : Provenance.provenance -> ergo_expr

  val evar : Provenance.provenance -> Names.relative_name -> ergo_expr

  val econst : Provenance.provenance -> data -> ergo_expr

  val enone : Provenance.provenance -> ergo_expr

  val esome : Provenance.provenance -> ergo_expr -> ergo_expr

  val earray :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr list -> ergo_expr

  val etext :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr list -> ergo_expr

  val eunaryoperator :
    Provenance.provenance -> ergo_unary_operator -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr

  val ebinaryoperator :
    Provenance.provenance -> ergo_binary_operator -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr -> ergo_expr

  val eunarybuiltin :
    Provenance.provenance -> QcertOps.Unary.op -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr

  val ebinarybuiltin :
    Provenance.provenance -> QcertOps.Binary.op -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr -> ergo_expr

  val eif :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr -> ergo_expr

  val elet :
    Provenance.provenance -> char list -> (Provenance.provenance,
    Names.relative_name) ErgoType.ergo_type option -> ergo_expr -> ergo_expr
    -> ergo_expr

  val eprint : Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr

  val enew :
    Provenance.provenance -> Names.relative_name ->
    (char list * (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr) list -> ergo_expr

  val erecord :
    Provenance.provenance -> (char list * (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
    ergo_expr

  val ecallfun :
    Provenance.provenance -> Names.relative_name -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr list ->
    ergo_expr

  val ematch :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ((Provenance.provenance,
    Names.relative_name) ergo_pattern * (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr -> ergo_expr

  val eforeach :
    Provenance.provenance -> (char list * (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr option -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ergo_expr

  val eas :
    Provenance.provenance -> char list -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr

  val opuminusi :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ergo_expr

  val sreturn :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ergo_stmt

  val efunreturn : provenance -> ergo_expr -> ergo_expr

  val sthrow :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ergo_stmt

  val scallclause :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> char list ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_expr list -> ergo_stmt

  val scallcontract :
    Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_stmt

  val ssetstate :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_stmt -> ergo_stmt

  val ssetstatedot :
    Provenance.provenance -> char list -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_stmt -> ergo_stmt

  val semit :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_stmt -> ergo_stmt

  val slet :
    Provenance.provenance -> char list -> (Provenance.provenance,
    Names.relative_name) ErgoType.ergo_type option -> ergo_expr -> ergo_stmt
    -> ergo_stmt

  val sprint : Provenance.provenance -> ergo_expr -> ergo_stmt -> ergo_stmt

  val sif :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_stmt ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_stmt -> ergo_stmt

  val senforce :
    Provenance.provenance -> ergo_expr -> ergo_stmt option -> ergo_stmt ->
    ergo_stmt

  val smatch :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_expr -> ((Provenance.provenance,
    Names.relative_name) ergo_pattern * (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_stmt) list ->
    (Provenance.provenance, Provenance.provenance, Names.relative_name)
    Ergo.ergo_stmt -> ergo_stmt

  val eoptionaldot :
    Provenance.provenance -> char list -> ergo_expr -> ergo_expr

  val eoptionaldefault :
    Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr

  val sreturnempty : Provenance.provenance -> ergo_stmt

  val efunreturnempty : Provenance.provenance -> ergo_expr

  val dnamespace : Provenance.provenance -> namespace_name -> ergo_declaration

  val dimport :
    Provenance.provenance -> Provenance.provenance import_decl ->
    ergo_declaration

  val dtype :
    Provenance.provenance -> (Provenance.provenance, Names.relative_name)
    ErgoType.ergo_type_declaration -> ergo_declaration

  val dstmt :
    Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
    Names.relative_name) Ergo.ergo_stmt -> ergo_declaration

  val dconstant :
    Provenance.provenance -> local_name -> (Provenance.provenance,
    Names.relative_name) ErgoType.ergo_type option -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    ergo_declaration

  val dfunc :
    Provenance.provenance -> local_name -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_function ->
    ergo_declaration

  val dcontract :
    Provenance.provenance -> local_name -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_contract ->
    ergo_declaration

  val dsetcontract :
    Provenance.provenance -> Names.relative_name -> (Provenance.provenance,
    Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
    ergo_declaration

  val ergo_module_to_es6 :
    ergo_input list -> (char list * ergo_expr) list option -> result_file
    Result0.eresult

  val ergo_module_to_java :
    ergo_input list -> (char list * ergo_expr) list option -> result_file
    Result0.eresult

  val ergo_module_to_wasm :
    ergo_input list -> (char list * ergo_expr) list option -> result_file
    Result0.eresult

  type ergo_brand_model = ErgoCType.tbrand_model

  val ergo_empty_brand_model : ErgoCType.tbrand_model

  val ergo_brand_model_from_inputs :
    ergo_input list -> (ergo_brand_model * laergo_type_declaration list)
    eresult

  val ergo_refresh_brand_model :
    ergo_brand_model -> repl_context -> (ergo_brand_model * repl_context)
    eresult

  val init_repl_context :
    ergo_brand_model -> ergo_input list -> repl_context Result0.eresult

  val ergo_repl_eval_decl :
    ergo_brand_model -> repl_context -> ergo_declaration -> char list
    Result0.eresult * repl_context
 end
