open Bag
open BinInt
open BinPos
open Bindings
open BrandRelation
open CoqLibAdd
open Data
open DataLift
open Datatypes
open ForeignData
open ForeignOperators
open Iterators
open Lift
open Nat
open OperatorsUtils
open SortBy
open String0
open StringAdd
open UnaryOperators

(** val nat_arith_unary_op_eval : nat_arith_unary_op -> int -> int **)

let nat_arith_unary_op_eval op z =
  match op with
  | NatAbs -> Z.abs z
  | NatLog2 -> Z.log2 z
  | NatSqrt -> Z.sqrt z

(** val float_arith_unary_op_eval : float_arith_unary_op -> float -> float **)

let float_arith_unary_op_eval op f =
  match op with
  | FloatNeg -> (fun x -> Float.neg x) f
  | FloatSqrt -> (fun x -> Float.sqrt x) f
  | FloatExp -> (fun x -> Float.exp x) f
  | FloatLog -> (fun x -> Float.log x) f
  | FloatLog10 -> (fun x -> Float.log10 x) f
  | FloatCeil -> (fun x -> Float.ceil x) f
  | FloatFloor -> (fun x -> Float.floor x) f
  | FloatAbs -> (fun x -> Float.abs x) f

(** val coq_ToString_data :
    foreign_data -> foreign_operators -> data coq_ToString **)

let coq_ToString_data _ foperators =
  foperators.foreign_operators_unary_data_tostring

(** val unary_op_eval :
    foreign_data -> brand_relation_t -> foreign_operators -> unary_op -> data
    -> data option **)

let unary_op_eval fdata h foperators uop d =
  match uop with
  | OpIdentity -> Some d
  | OpNeg -> unudbool fdata negb d
  | OpRec s -> Some (Coq_drec ((s, d) :: []))
  | OpDot s -> (match d with
                | Coq_drec r -> edot r s
                | _ -> None)
  | OpRecRemove s ->
    (match d with
     | Coq_drec r -> Some (Coq_drec (rremove r s))
     | _ -> None)
  | OpRecProject sl ->
    (match d with
     | Coq_drec r -> Some (Coq_drec (rproject r sl))
     | _ -> None)
  | OpBag -> Some (Coq_dcoll (d :: []))
  | OpSingleton ->
    (match d with
     | Coq_dcoll l ->
       (match l with
        | [] -> Some (dnone fdata)
        | d' :: l0 ->
          (match l0 with
           | [] -> Some (dsome fdata d')
           | _ :: _ -> Some (dnone fdata)))
     | _ -> None)
  | OpFlatten ->
    lift_oncoll fdata (fun l ->
      lift (fun x -> Coq_dcoll x) (oflatten fdata l)) d
  | OpDistinct -> rondcoll fdata (bdistinct (data_eq_dec fdata)) d
  | OpOrderBy sc -> data_sort fdata sc d
  | OpCount ->
    lift (fun x -> Coq_dnat x)
      (ondcoll fdata (fun z -> Z.of_nat (bcount z)) d)
  | OpToString ->
    Some (Coq_dstring (foperators.foreign_operators_unary_data_tostring d))
  | OpToText ->
    Some (Coq_dstring (foperators.foreign_operators_unary_data_totext d))
  | OpLength -> unndstring fdata (fun s -> Z.of_nat (length s)) d
  | OpSubstring (start, olen) ->
    (match d with
     | Coq_dstring s ->
       Some (Coq_dstring
         (let real_start =
            (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
              (fun _ -> 0)
              (fun p -> Pos.to_nat p)
              (fun n -> sub (length s) (Pos.to_nat n))
              start
          in
          let real_olen =
            match olen with
            | Some len ->
              ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
                 (fun _ -> 0)
                 (fun p -> Pos.to_nat p)
                 (fun _ -> 0)
                 len)
            | None -> sub (length s) real_start
          in
          substring real_start real_olen s))
     | _ -> None)
  | OpLike pat ->
    (match d with
     | Coq_dstring s -> Some (Coq_dbool (string_like s pat None))
     | _ -> None)
  | OpLeft -> Some (Coq_dleft d)
  | OpRight -> Some (Coq_dright d)
  | OpBrand b -> Some (Coq_dbrand ((canon_brands h b), d))
  | OpUnbrand -> (match d with
                  | Coq_dbrand (_, d') -> Some d'
                  | _ -> None)
  | OpCast b ->
    (match d with
     | Coq_dbrand (b', _) ->
       if sub_brands_dec h b' b
       then Some (dsome fdata d)
       else Some (dnone fdata)
     | _ -> None)
  | OpNatUnary op ->
    (match d with
     | Coq_dnat n -> Some (Coq_dnat (nat_arith_unary_op_eval op n))
     | _ -> None)
  | OpNatSum -> lift (fun x -> Coq_dnat x) (lift_oncoll fdata (dsum fdata) d)
  | OpNatMin -> (match d with
                 | Coq_dcoll l -> lifted_min fdata l
                 | _ -> None)
  | OpNatMax -> (match d with
                 | Coq_dcoll l -> lifted_max fdata l
                 | _ -> None)
  | OpNatMean ->
    lift (fun x -> Coq_dnat x) (lift_oncoll fdata (darithmean fdata) d)
  | OpFloatOfNat ->
    (match d with
     | Coq_dnat n -> Some (Coq_dfloat ((fun x -> float_of_int x) n))
     | _ -> None)
  | OpFloatUnary op ->
    (match d with
     | Coq_dfloat n -> Some (Coq_dfloat (float_arith_unary_op_eval op n))
     | _ -> None)
  | OpFloatTruncate ->
    (match d with
     | Coq_dfloat f -> Some (Coq_dnat ((fun x -> truncate x) f))
     | _ -> None)
  | OpFloatSum -> lift_oncoll fdata (lifted_fsum fdata) d
  | OpFloatMean -> lift_oncoll fdata (lifted_farithmean fdata) d
  | OpFloatBagMin -> lift_oncoll fdata (lifted_fmin fdata) d
  | OpFloatBagMax -> lift_oncoll fdata (lifted_fmax fdata) d
  | OpForeignUnary fu -> foperators.foreign_operators_unary_interp h fu d
