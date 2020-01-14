open BinaryOperators
open Bindings
open BrandRelation
open Data
open DataResult
open Datatypes
open List0
open QcertData
open QcertDataTyping
open QcertType
open QcertTyping
open RSubtype
open RType
open RTypeMeetJoin
open Schema
open String0
open TBrandContext
open TBrandModel
open TBrandModelProp
open TDataInfer
open TOperatorsInferSub
open TUtil
open UnaryOperators

module QType =
 functor (Coq_ergomodel:QBackendModel.QBackendModel) ->
 struct
  (** val empty_brand_model : unit -> brand_model **)

  let empty_brand_model _ =
    empty_brand_model enhanced_foreign_type

  type record_kind = RType.record_kind

  (** val open_kind : record_kind **)

  let open_kind =
    Open

  (** val closed_kind : record_kind **)

  let closed_kind =
    Closed

  type qtype_struct = rtype_UU2080_

  type qtype = rtype

  type t = qtype

  (** val tbottom : brand_relation -> qtype **)

  let tbottom br =
    coq_Bottom enhanced_foreign_type br

  (** val ttop : brand_relation -> qtype **)

  let ttop br =
    coq_Top enhanced_foreign_type br

  (** val tunit : brand_relation -> qtype **)

  let tunit br =
    coq_Unit enhanced_foreign_type br

  (** val tfloat : brand_relation -> qtype **)

  let tfloat br =
    coq_Float enhanced_foreign_type br

  (** val tnat : brand_relation -> qtype **)

  let tnat br =
    coq_Nat enhanced_foreign_type br

  (** val tbool : brand_relation -> qtype **)

  let tbool br =
    coq_Bool enhanced_foreign_type br

  (** val tstring : brand_relation -> qtype **)

  let tstring br =
    coq_String enhanced_foreign_type br

  (** val tdateTimeFormat : brand_relation -> qtype **)

  let tdateTimeFormat =
    coq_DateTimeFormat

  (** val tdateTime : brand_relation -> qtype **)

  let tdateTime =
    coq_DateTime

  (** val tduration : brand_relation -> qtype **)

  let tduration =
    coq_DateTimeDuration

  (** val tperiod : brand_relation -> qtype **)

  let tperiod =
    coq_DateTimePeriod

  (** val tcoll : brand_relation -> qtype -> qtype **)

  let tcoll br =
    coq_Coll enhanced_foreign_type br

  (** val trec :
      brand_relation -> record_kind -> (char list * qtype) list -> qtype **)

  let trec br x r =
    coq_Rec enhanced_foreign_type br x r

  (** val teither : brand_relation -> qtype -> qtype -> qtype **)

  let teither br =
    coq_Either enhanced_foreign_type br

  (** val tarrow : brand_relation -> qtype -> qtype -> qtype **)

  let tarrow br =
    coq_Arrow enhanced_foreign_type br

  (** val tbrand : brand_relation -> char list list -> qtype **)

  let tbrand br =
    coq_Brand enhanced_foreign_type br

  (** val toption : brand_relation -> qtype -> qtype **)

  let toption br =
    coq_Option enhanced_foreign_type br

  (** val qcert_type_meet : brand_relation -> qtype -> qtype -> qtype **)

  let qcert_type_meet br =
    rtype_meet enhanced_foreign_type br

  (** val qcert_type_join : brand_relation -> qtype -> qtype -> qtype **)

  let qcert_type_join br =
    rtype_join enhanced_foreign_type br

  (** val qcert_type_subtype_dec : brand_model -> qtype -> qtype -> bool **)

  let qcert_type_subtype_dec m t1 t2 =
    subtype_dec enhanced_foreign_type m.brand_model_relation t1 t2

  (** val untcoll : brand_model -> qtype -> qtype option **)

  let untcoll =
    QcertTyping.tuncoll

  (** val unteither : brand_model -> qtype -> (qtype * qtype) option **)

  let unteither m =
    tuneither enhanced_foreign_type m

  (** val untrec :
      brand_model -> qtype -> (record_kind * (char list * qtype) list) option **)

  let untrec m =
    tunrec enhanced_foreign_type m

  (** val qcert_type_infer_data : brand_model -> data -> qtype option **)

  let qcert_type_infer_data m =
    infer_data_type enhanced_foreign_data enhanced_foreign_type
      enhanced_foreign_data_typing m

  (** val qcert_type_infer_binary_op :
      brand_model -> binary_op -> qtype -> qtype -> ((qtype * qtype) * qtype)
      option **)

  let qcert_type_infer_binary_op m =
    infer_binary_op_type_sub enhanced_foreign_data enhanced_foreign_type
      enhanced_foreign_data_typing m enhanced_foreign_operators
      (enhanced_foreign_operators_typing m)

  (** val qcert_type_infer_unary_op :
      brand_model -> unary_op -> qtype -> (qtype * qtype) option **)

  let qcert_type_infer_unary_op m =
    infer_unary_op_type_sub enhanced_foreign_data enhanced_foreign_type
      enhanced_foreign_data_typing m enhanced_foreign_operators
      (enhanced_foreign_operators_typing m)

  (** val unpack_qcert_type : brand_relation -> qtype -> qtype_struct **)

  let unpack_qcert_type _ t0 =
    t0

  type tbrand_relation = brand_relation

  (** val tempty_brand_relation : tbrand_relation **)

  let tempty_brand_relation =
    []

  (** val mk_tbrand_relation :
      (char list * char list) list -> tbrand_relation qresult **)

  let mk_tbrand_relation =
    mk_brand_relation enhanced_foreign_data

  type tbrand_context_decls = brand_context_decls

  type tbrand_context = brand_context

  (** val mk_tbrand_context :
      brand_relation -> tbrand_context_decls -> tbrand_context **)

  let mk_tbrand_context br =
    mk_brand_context enhanced_foreign_type br

  type tbrand_model = brand_model

  (** val mk_tbrand_model :
      brand_relation -> tbrand_context_decls -> tbrand_model qresult **)

  let mk_tbrand_model br =
    make_brand_model_from_decls_fails enhanced_foreign_data
      enhanced_foreign_type br

  (** val tempty_brand_model : tbrand_model **)

  let tempty_brand_model =
    make_brand_model enhanced_foreign_type tempty_brand_relation []

  (** val qcert_type_unpack : brand_relation -> qtype -> qtype_struct **)

  let qcert_type_unpack _ t0 =
    t0

  (** val qcert_type_closed_from_open : brand_model -> qtype -> qtype **)

  let qcert_type_closed_from_open m t0 =
    let filtered_var = untrec m t0 in
    (match filtered_var with
     | Some p ->
       let (_, fields) = p in
       coq_Rec enhanced_foreign_type m.brand_model_relation Closed fields
     | None -> t0)

  (** val infer_brand_strict :
      brand_model -> brands -> qtype -> (rtype * qtype) option **)

  let infer_brand_strict m b t0 =
    if subtype_dec enhanced_foreign_type m.brand_model_relation t0
         (qcert_type_closed_from_open m
           (brands_type enhanced_foreign_type m b))
    then Some ((coq_Brand enhanced_foreign_type m.brand_model_relation b), t0)
    else None

  (** val recminus :
      brand_relation -> (char list * rtype) list -> char list list ->
      (char list * rtype) list **)

  let recminus _ rt sl =
    fold_left rremove sl rt

  (** val diff_record_types :
      brand_model -> brands -> qtype -> (char list list * char list list)
      option **)

  let diff_record_types m b t0 =
    match tunrec enhanced_foreign_type m t0 with
    | Some p ->
      let (_, actual_rt) = p in
      (match tunrec enhanced_foreign_type m
               (qcert_type_closed_from_open m
                 (brands_type enhanced_foreign_type m b)) with
       | Some p0 ->
         let (_, expected_rt) = p0 in
         let in_expected_not_in_actual =
           recminus m.brand_model_relation expected_rt (map fst actual_rt)
         in
         let in_actual_not_in_expected =
           recminus m.brand_model_relation actual_rt (map fst expected_rt)
         in
         Some ((map fst in_expected_not_in_actual),
         (map fst in_actual_not_in_expected))
       | None -> None)
    | None -> None

  (** val rec_fields_that_are_not_subtype :
      brand_model -> (char list * qtype) list -> (char list * qtype) list ->
      ((char list * qtype) * qtype) list **)

  let rec rec_fields_that_are_not_subtype m t1 t2 =
    match t1 with
    | [] -> []
    | p :: rest1 ->
      let (name1, t3) = p in
      (match t2 with
       | [] -> []
       | p0 :: rest2 ->
         let (name2, t4) = p0 in
         if string_dec name1 name2
         then if subtype_dec enhanced_foreign_type m.brand_model_relation t4
                   t3
              then rec_fields_that_are_not_subtype m rest1 rest2
              else ((name1, t3),
                     t4) :: (rec_fields_that_are_not_subtype m rest1 rest2)
         else rec_fields_that_are_not_subtype m rest1 rest2)

  (** val fields_that_are_not_subtype :
      brand_model -> brands -> qtype -> ((char list * qtype) * qtype) list **)

  let fields_that_are_not_subtype m b t0 =
    match tunrec enhanced_foreign_type m t0 with
    | Some p ->
      let (_, actual_rt) = p in
      (match tunrec enhanced_foreign_type m
               (qcert_type_closed_from_open m
                 (brands_type enhanced_foreign_type m b)) with
       | Some p0 ->
         let (_, expected_rt) = p0 in
         rec_fields_that_are_not_subtype m expected_rt actual_rt
       | None -> [])
    | None -> []
 end
