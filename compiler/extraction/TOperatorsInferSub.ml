open BinaryOperators
open Datatypes
open EquivDec
open ForeignData
open ForeignDataTyping
open ForeignOperators
open ForeignOperatorsTyping
open ForeignType
open Lattice
open Lift
open List0
open RSubtype
open RType
open RTypeLattice
open TBrandModel
open TBrandModelProp
open TOperatorsInfer
open TUtil
open UnaryOperators

(** val infer_binary_op_type_sub :
    foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
    foreign_operators -> foreign_operators_typing -> binary_op -> rtype ->
    rtype -> ((rtype * rtype) * rtype) option **)

let infer_binary_op_type_sub _ ftype _ m _ foptyping b _UU03c4__UU2081_ _UU03c4__UU2082_ =
  match b with
  | OpEqual ->
    let _UU03c4_common =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        _UU03c4__UU2082_
    in
    Some (((coq_Bool ftype m.brand_model_relation), _UU03c4_common),
    _UU03c4_common)
  | OpRecConcat ->
    if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
         _UU03c4__UU2081_ (coq_Bottom ftype m.brand_model_relation)
    then if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
              _UU03c4__UU2082_ (coq_Bottom ftype m.brand_model_relation)
         then Some (((coq_Bottom ftype m.brand_model_relation),
                (coq_Bottom ftype m.brand_model_relation)),
                (coq_Bottom ftype m.brand_model_relation))
         else lift (fun _ -> ((_UU03c4__UU2082_,
                (coq_Bottom ftype m.brand_model_relation)),
                _UU03c4__UU2082_)) (tunrec ftype m _UU03c4__UU2082_)
    else if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
              _UU03c4__UU2082_ (coq_Bottom ftype m.brand_model_relation)
         then lift (fun _ -> ((_UU03c4__UU2081_, _UU03c4__UU2081_),
                (coq_Bottom ftype m.brand_model_relation)))
                (tunrec ftype m _UU03c4__UU2081_)
         else lift (fun _UU03c4_ -> ((_UU03c4_, _UU03c4__UU2081_),
                _UU03c4__UU2082_))
                (trecConcatRight ftype m _UU03c4__UU2081_ _UU03c4__UU2082_)
  | OpRecMerge ->
    if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
         _UU03c4__UU2081_ (coq_Bottom ftype m.brand_model_relation)
    then if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
              _UU03c4__UU2082_ (coq_Bottom ftype m.brand_model_relation)
         then Some
                (((coq_Coll ftype m.brand_model_relation
                    (coq_Bottom ftype m.brand_model_relation)),
                (coq_Bottom ftype m.brand_model_relation)),
                (coq_Bottom ftype m.brand_model_relation))
         else lift (fun _ ->
                (((coq_Coll ftype m.brand_model_relation _UU03c4__UU2082_),
                (coq_Bottom ftype m.brand_model_relation)),
                _UU03c4__UU2082_)) (tunrec ftype m _UU03c4__UU2082_)
    else if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
              _UU03c4__UU2082_ (coq_Bottom ftype m.brand_model_relation)
         then lift (fun _ ->
                (((coq_Coll ftype m.brand_model_relation _UU03c4__UU2081_),
                _UU03c4__UU2081_),
                (coq_Bottom ftype m.brand_model_relation)))
                (tunrec ftype m _UU03c4__UU2081_)
         else lift (fun _UU03c4_ ->
                (((coq_Coll ftype m.brand_model_relation _UU03c4_),
                _UU03c4__UU2081_), _UU03c4__UU2082_))
                (tmergeConcat ftype m _UU03c4__UU2081_ _UU03c4__UU2082_)
  | OpAnd ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Bool ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Bool ftype m.brand_model_relation)
         then Some (((coq_Bool ftype m.brand_model_relation),
                (coq_Bool ftype m.brand_model_relation)),
                (coq_Bool ftype m.brand_model_relation))
         else None
    else None
  | OpOr ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Bool ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Bool ftype m.brand_model_relation)
         then Some (((coq_Bool ftype m.brand_model_relation),
                (coq_Bool ftype m.brand_model_relation)),
                (coq_Bool ftype m.brand_model_relation))
         else None
    else None
  | OpLt ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Nat ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Nat ftype m.brand_model_relation)
         then Some (((coq_Bool ftype m.brand_model_relation),
                (coq_Nat ftype m.brand_model_relation)),
                (coq_Nat ftype m.brand_model_relation))
         else None
    else None
  | OpLe ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Nat ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Nat ftype m.brand_model_relation)
         then Some (((coq_Bool ftype m.brand_model_relation),
                (coq_Nat ftype m.brand_model_relation)),
                (coq_Nat ftype m.brand_model_relation))
         else None
    else None
  | OpBagNth ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
         (coq_Nat ftype m.brand_model_relation)
    then let _UU03c4__UU2081_' =
           (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
             (coq_Coll ftype m.brand_model_relation
               (coq_Bottom ftype m.brand_model_relation))
         in
         lift (fun _UU03c4_ -> ((_UU03c4_, _UU03c4__UU2081_'),
           (coq_Nat ftype m.brand_model_relation)))
           (tsingleton ftype m _UU03c4__UU2081_')
    else None
  | OpContains ->
    if equiv_decb (rtype_eq_dec ftype m.brand_model_relation)
         _UU03c4__UU2082_ (coq_Bottom ftype m.brand_model_relation)
    then Some (((coq_Bool ftype m.brand_model_relation), _UU03c4__UU2081_),
           _UU03c4__UU2082_)
    else lift (fun _UU03c4__UU2082_' ->
           let _UU03c4_ =
             (rtype_lattice ftype m.brand_model_relation).join
               _UU03c4__UU2081_ _UU03c4__UU2082_'
           in
           (((coq_Bool ftype m.brand_model_relation), _UU03c4_),
           (coq_Coll ftype m.brand_model_relation _UU03c4_)))
           (tuncoll ftype m _UU03c4__UU2082_)
  | OpStringConcat ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_String ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_String ftype m.brand_model_relation)
         then Some (((coq_String ftype m.brand_model_relation),
                (coq_String ftype m.brand_model_relation)),
                (coq_String ftype m.brand_model_relation))
         else None
    else None
  | OpStringJoin ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_String ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Coll ftype m.brand_model_relation
                (coq_String ftype m.brand_model_relation))
         then Some (((coq_String ftype m.brand_model_relation),
                (coq_String ftype m.brand_model_relation)),
                (coq_Coll ftype m.brand_model_relation
                  (coq_String ftype m.brand_model_relation)))
         else None
    else None
  | OpNatBinary _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Nat ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Nat ftype m.brand_model_relation)
         then Some (((coq_Nat ftype m.brand_model_relation),
                (coq_Nat ftype m.brand_model_relation)),
                (coq_Nat ftype m.brand_model_relation))
         else None
    else None
  | OpFloatBinary _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Float ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Float ftype m.brand_model_relation)
         then Some (((coq_Float ftype m.brand_model_relation),
                (coq_Float ftype m.brand_model_relation)),
                (coq_Float ftype m.brand_model_relation))
         else None
    else None
  | OpFloatCompare _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Float ftype m.brand_model_relation)
    then if subtype_dec ftype m.brand_model_relation _UU03c4__UU2082_
              (coq_Float ftype m.brand_model_relation)
         then Some (((coq_Bool ftype m.brand_model_relation),
                (coq_Float ftype m.brand_model_relation)),
                (coq_Float ftype m.brand_model_relation))
         else None
    else None
  | OpForeignBinary fb ->
    foptyping.foreign_operators_typing_binary_infer_sub fb _UU03c4__UU2081_
      _UU03c4__UU2082_
  | _ ->
    let _UU03c4_common =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        _UU03c4__UU2082_
    in
    (match tuncoll ftype m _UU03c4_common with
     | Some _ -> Some ((_UU03c4_common, _UU03c4_common), _UU03c4_common)
     | None -> None)

(** val infer_unary_op_type_sub :
    foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
    foreign_operators -> foreign_operators_typing -> unary_op -> rtype ->
    (rtype * rtype) option **)

let infer_unary_op_type_sub _ ftype _ m _ foptyping u _UU03c4__UU2081_ =
  match u with
  | OpIdentity -> Some (_UU03c4__UU2081_, _UU03c4__UU2081_)
  | OpNeg ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Bool ftype m.brand_model_relation)
    then Some ((coq_Bool ftype m.brand_model_relation),
           (coq_Bool ftype m.brand_model_relation))
    else None
  | OpRec s ->
    Some
      ((coq_Rec ftype m.brand_model_relation Closed ((s,
         _UU03c4__UU2081_) :: [])), _UU03c4__UU2081_)
  | OpDot s ->
    if equiv_dec (rtype_eq_dec ftype m.brand_model_relation) _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)
    then Some ((coq_Bottom ftype m.brand_model_relation),
           (coq_Bottom ftype m.brand_model_relation))
    else lift (fun _UU03c4_ -> (_UU03c4_, _UU03c4__UU2081_))
           (tunrecdot ftype m s _UU03c4__UU2081_)
  | OpRecRemove s ->
    if equiv_dec (rtype_eq_dec ftype m.brand_model_relation) _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)
    then Some ((coq_Bottom ftype m.brand_model_relation),
           (coq_Bottom ftype m.brand_model_relation))
    else lift (fun _UU03c4_ -> (_UU03c4_, _UU03c4__UU2081_))
           (tunrecremove ftype m s _UU03c4__UU2081_)
  | OpRecProject sl ->
    if equiv_dec (rtype_eq_dec ftype m.brand_model_relation) _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)
    then Some ((coq_Bottom ftype m.brand_model_relation),
           (coq_Bottom ftype m.brand_model_relation))
    else lift (fun _UU03c4_ -> (_UU03c4_, _UU03c4__UU2081_))
           (tunrecproject ftype m sl _UU03c4__UU2081_)
  | OpBag ->
    Some ((coq_Coll ftype m.brand_model_relation _UU03c4__UU2081_),
      _UU03c4__UU2081_)
  | OpSingleton ->
    let _UU03c4__UU2081_' =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        (coq_Coll ftype m.brand_model_relation
          (coq_Bottom ftype m.brand_model_relation))
    in
    lift (fun _UU03c4_ -> (_UU03c4_, _UU03c4__UU2081_'))
      (tsingleton ftype m _UU03c4__UU2081_')
  | OpFlatten ->
    let _UU03c4__UU2081_' =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        (coq_Coll ftype m.brand_model_relation
          (coq_Coll ftype m.brand_model_relation
            (coq_Bottom ftype m.brand_model_relation)))
    in
    bind (tuncoll ftype m _UU03c4__UU2081_') (fun _UU03c4__UU2081_in ->
      lift (fun _ -> (_UU03c4__UU2081_in, _UU03c4__UU2081_'))
        (tuncoll ftype m _UU03c4__UU2081_in))
  | OpDistinct ->
    let _UU03c4__UU2081_' =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        (coq_Coll ftype m.brand_model_relation
          (coq_Bottom ftype m.brand_model_relation))
    in
    lift (fun _UU03c4_ -> ((coq_Coll ftype m.brand_model_relation _UU03c4_),
      _UU03c4__UU2081_')) (tuncoll ftype m _UU03c4__UU2081_')
  | OpOrderBy sl ->
    let _UU03c4__UU2081_' =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        (coq_Coll ftype m.brand_model_relation
          (coq_Bottom ftype m.brand_model_relation))
    in
    (match tuncoll ftype m _UU03c4__UU2081_' with
     | Some _UU03c4__UU2081__UU2080_ ->
       (match tunrecsortable ftype m (map fst sl) _UU03c4__UU2081__UU2080_ with
        | Some _ -> Some (_UU03c4__UU2081_', _UU03c4__UU2081_')
        | None -> None)
     | None -> None)
  | OpCount ->
    let _UU03c4__UU2081_' =
      (rtype_lattice ftype m.brand_model_relation).join _UU03c4__UU2081_
        (coq_Coll ftype m.brand_model_relation
          (coq_Bottom ftype m.brand_model_relation))
    in
    lift (fun _ -> ((coq_Nat ftype m.brand_model_relation),
      _UU03c4__UU2081_')) (tuncoll ftype m _UU03c4__UU2081_')
  | OpToString ->
    Some ((coq_String ftype m.brand_model_relation), _UU03c4__UU2081_)
  | OpToText ->
    Some ((coq_String ftype m.brand_model_relation), _UU03c4__UU2081_)
  | OpLength ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_String ftype m.brand_model_relation)
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_String ftype m.brand_model_relation))
    else None
  | OpSubstring (_, _) ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_String ftype m.brand_model_relation)
    then Some ((coq_String ftype m.brand_model_relation),
           (coq_String ftype m.brand_model_relation))
    else None
  | OpLike _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_String ftype m.brand_model_relation)
    then Some ((coq_Bool ftype m.brand_model_relation),
           (coq_String ftype m.brand_model_relation))
    else None
  | OpLeft ->
    Some
      ((coq_Either ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)), _UU03c4__UU2081_)
  | OpRight ->
    Some
      ((coq_Either ftype m.brand_model_relation
         (coq_Bottom ftype m.brand_model_relation) _UU03c4__UU2081_),
      _UU03c4__UU2081_)
  | OpBrand b ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (brands_type ftype m b)
    then Some ((coq_Brand ftype m.brand_model_relation b), _UU03c4__UU2081_)
    else None
  | OpUnbrand ->
    if equiv_dec (rtype_eq_dec ftype m.brand_model_relation) _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)
    then Some ((coq_Bottom ftype m.brand_model_relation),
           (coq_Bottom ftype m.brand_model_relation))
    else (match _UU03c4__UU2081_ with
          | Brand_UU2080_ b ->
            Some ((brands_type ftype m b), _UU03c4__UU2081_)
          | _ -> None)
  | OpCast b ->
    if equiv_dec (rtype_eq_dec ftype m.brand_model_relation) _UU03c4__UU2081_
         (coq_Bottom ftype m.brand_model_relation)
    then Some ((coq_Bottom ftype m.brand_model_relation),
           (coq_Bottom ftype m.brand_model_relation))
    else (match _UU03c4__UU2081_ with
          | Brand_UU2080_ _ ->
            Some
              ((coq_Option ftype m.brand_model_relation
                 (coq_Brand ftype m.brand_model_relation b)),
              _UU03c4__UU2081_)
          | _ -> None)
  | OpNatUnary _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Nat ftype m.brand_model_relation)
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Nat ftype m.brand_model_relation))
    else None
  | OpNatSum ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Coll ftype m.brand_model_relation
           (coq_Nat ftype m.brand_model_relation))
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Coll ftype m.brand_model_relation
             (coq_Nat ftype m.brand_model_relation)))
    else None
  | OpNatMin ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Coll ftype m.brand_model_relation
           (coq_Nat ftype m.brand_model_relation))
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Coll ftype m.brand_model_relation
             (coq_Nat ftype m.brand_model_relation)))
    else None
  | OpNatMax ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Coll ftype m.brand_model_relation
           (coq_Nat ftype m.brand_model_relation))
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Coll ftype m.brand_model_relation
             (coq_Nat ftype m.brand_model_relation)))
    else None
  | OpNatMean ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Coll ftype m.brand_model_relation
           (coq_Nat ftype m.brand_model_relation))
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Coll ftype m.brand_model_relation
             (coq_Nat ftype m.brand_model_relation)))
    else None
  | OpFloatOfNat ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Nat ftype m.brand_model_relation)
    then Some ((coq_Float ftype m.brand_model_relation),
           (coq_Nat ftype m.brand_model_relation))
    else None
  | OpFloatUnary _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Float ftype m.brand_model_relation)
    then Some ((coq_Float ftype m.brand_model_relation),
           (coq_Float ftype m.brand_model_relation))
    else None
  | OpFloatTruncate ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Float ftype m.brand_model_relation)
    then Some ((coq_Nat ftype m.brand_model_relation),
           (coq_Float ftype m.brand_model_relation))
    else None
  | OpForeignUnary fu ->
    foptyping.foreign_operators_typing_unary_infer_sub fu _UU03c4__UU2081_
  | _ ->
    if subtype_dec ftype m.brand_model_relation _UU03c4__UU2081_
         (coq_Coll ftype m.brand_model_relation
           (coq_Float ftype m.brand_model_relation))
    then Some ((coq_Float ftype m.brand_model_relation),
           (coq_Coll ftype m.brand_model_relation
             (coq_Float ftype m.brand_model_relation)))
    else None
