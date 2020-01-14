open Bag
open BinInt
open BinaryOperators
open Bindings
open BrandRelation
open CoqLibAdd
open Data
open DataLift
open Datatypes
open ForeignData
open ForeignOperators
open List0
open OperatorsUtils
open String0
open ZArith_dec

(** val nat_arith_binary_op_eval :
    nat_arith_binary_op -> int -> int -> int **)

let nat_arith_binary_op_eval op z1 z2 =
  match op with
  | NatPlus -> Z.add z1 z2
  | NatMinus -> Z.sub z1 z2
  | NatMult -> Z.mul z1 z2
  | NatDiv -> Z.quot z1 z2
  | NatRem -> Z.rem z1 z2
  | NatMin -> Z.min z1 z2
  | NatMax -> Z.max z1 z2

(** val float_arith_binary_op_eval :
    float_arith_binary_op -> float -> float -> float **)

let float_arith_binary_op_eval op f1 f2 =
  match op with
  | FloatPlus -> (fun x y -> x +. y) f1 f2
  | FloatMinus -> (fun x y -> x -. y) f1 f2
  | FloatMult -> (fun x y -> x *. y) f1 f2
  | FloatDiv -> (fun x y -> x /. y) f1 f2
  | FloatPow -> (fun x y -> x ** y) f1 f2
  | FloatMin -> (fun x y -> min x y) f1 f2
  | FloatMax -> (fun x y -> max x y) f1 f2

(** val float_compare_binary_op_eval :
    float_compare_binary_op -> float -> float -> bool **)

let float_compare_binary_op_eval op f1 f2 =
  match op with
  | FloatLt -> (fun x y -> x < y) f1 f2
  | FloatLe -> (fun x y -> x <= y) f1 f2
  | FloatGt -> (fun x y -> x > y) f1 f2
  | FloatGe -> (fun x y -> x >= y) f1 f2

(** val binary_op_eval :
    brand_relation_t -> foreign_data -> foreign_operators -> binary_op ->
    data -> data -> data option **)

let binary_op_eval h fdata foperators bop d1 d2 =
  match bop with
  | OpEqual ->
    unbdata fdata (fun x y -> if data_eq_dec fdata x y then true else false)
      d1 d2
  | OpRecConcat ->
    (match d1 with
     | Coq_drec r1 ->
       (match d2 with
        | Coq_drec r2 -> Some (Coq_drec (rec_sort coq_ODT_string (app r1 r2)))
        | _ -> None)
     | _ -> None)
  | OpRecMerge ->
    (match d1 with
     | Coq_drec r1 ->
       (match d2 with
        | Coq_drec r2 ->
          (match merge_bindings (data_eqdec fdata) r1 r2 with
           | Some x -> Some (Coq_dcoll ((Coq_drec x) :: []))
           | None -> Some (Coq_dcoll []))
        | _ -> None)
     | _ -> None)
  | OpAnd -> unbdbool fdata (&&) d1 d2
  | OpOr -> unbdbool fdata (||) d1 d2
  | OpLt ->
    unbdnat fdata (fun x y -> if coq_Z_lt_dec x y then true else false) d1 d2
  | OpLe ->
    unbdnat fdata (fun x y -> if coq_Z_le_dec x y then true else false) d1 d2
  | OpBagUnion -> rondcoll2 fdata bunion d1 d2
  | OpBagDiff -> rondcoll2 fdata (bminus (data_eq_dec fdata)) d2 d1
  | OpBagMin -> rondcoll2 fdata (bmin (data_eq_dec fdata)) d1 d2
  | OpBagMax -> rondcoll2 fdata (bmax (data_eq_dec fdata)) d1 d2
  | OpBagNth ->
    (match d1 with
     | Coq_dcoll c ->
       (match d2 with
        | Coq_dnat n ->
          let natish = coq_ZToSignedNat n in
          if fst natish
          then (match nth_error c (snd natish) with
                | Some d -> Some (dsome fdata d)
                | None -> Some (dnone fdata))
          else Some (dnone fdata)
        | _ -> None)
     | _ -> None)
  | OpContains ->
    ondcoll fdata (fun l ->
      if in_dec (data_eq_dec fdata) d1 l
      then Coq_dbool true
      else Coq_dbool false) d2
  | OpStringConcat -> unsdstring fdata append d1 d2
  | OpStringJoin ->
    (match d1 with
     | Coq_dstring sep ->
       (match d2 with
        | Coq_dcoll c -> lifted_join fdata sep c
        | _ -> None)
     | _ -> None)
  | OpNatBinary op ->
    (match d1 with
     | Coq_dnat n1 ->
       (match d2 with
        | Coq_dnat n2 -> Some (Coq_dnat (nat_arith_binary_op_eval op n1 n2))
        | _ -> None)
     | _ -> None)
  | OpFloatBinary op ->
    (match d1 with
     | Coq_dfloat f1 ->
       (match d2 with
        | Coq_dfloat f2 ->
          Some (Coq_dfloat (float_arith_binary_op_eval op f1 f2))
        | _ -> None)
     | _ -> None)
  | OpFloatCompare op ->
    (match d1 with
     | Coq_dfloat f1 ->
       (match d2 with
        | Coq_dfloat f2 ->
          Some (Coq_dbool (float_compare_binary_op_eval op f1 f2))
        | _ -> None)
     | _ -> None)
  | OpForeignBinary fb ->
    foperators.foreign_operators_binary_interp h fb d1 d2
