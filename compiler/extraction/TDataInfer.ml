open BrandRelation
open Data
open ForeignData
open ForeignDataTyping
open ForeignType
open Lattice
open Lift
open RSubtype
open RType
open RTypeLattice
open TBrandModel
open TBrandModelProp

(** val infer_data_type :
    foreign_data -> foreign_type -> foreign_data_typing -> brand_model ->
    data -> rtype option **)

let rec infer_data_type fdata ftype fdtyping m = function
| Coq_dunit -> Some (coq_Unit ftype m.brand_model_relation)
| Coq_dnat _ -> Some (coq_Nat ftype m.brand_model_relation)
| Coq_dfloat _ -> Some (coq_Float ftype m.brand_model_relation)
| Coq_dbool _ -> Some (coq_Bool ftype m.brand_model_relation)
| Coq_dstring _ -> Some (coq_String ftype m.brand_model_relation)
| Coq_dcoll ld ->
  lift (coq_Coll ftype m.brand_model_relation)
    (let rec infer_data_type_dcoll = function
     | [] -> Some (coq_Bottom ftype m.brand_model_relation)
     | d0 :: ld' ->
       lift2 (rtype_lattice ftype m.brand_model_relation).join
         (infer_data_type fdata ftype fdtyping m d0)
         (infer_data_type_dcoll ld')
     in infer_data_type_dcoll ld)
| Coq_drec lsd ->
  (match let rec infer_data_type_drec = function
         | [] -> Some []
         | y :: lsd' ->
           let (s, d0) = y in
           (match infer_data_type fdata ftype fdtyping m d0 with
            | Some r ->
              (match infer_data_type_drec lsd' with
               | Some lsr' -> Some ((s, r) :: lsr')
               | None -> None)
            | None -> None)
         in infer_data_type_drec lsd with
   | Some l -> coq_RecMaybe ftype m.brand_model_relation Closed l
   | None -> None)
| Coq_dleft d0 ->
  lift (fun t ->
    coq_Either ftype m.brand_model_relation t
      (coq_Bottom ftype m.brand_model_relation))
    (infer_data_type fdata ftype fdtyping m d0)
| Coq_dright d0 ->
  lift (fun t ->
    coq_Either ftype m.brand_model_relation
      (coq_Bottom ftype m.brand_model_relation) t)
    (infer_data_type fdata ftype fdtyping m d0)
| Coq_dbrand (b, d0) ->
  if is_canon_brands_dec (brand_relation_brands m.brand_model_relation) b
  then (match infer_data_type fdata ftype fdtyping m d0 with
        | Some t ->
          if subtype_dec ftype m.brand_model_relation t
               (brands_type ftype m b)
          then Some (coq_Brand ftype m.brand_model_relation b)
          else Some (coq_Top ftype m.brand_model_relation)
        | None -> None)
  else None
| Coq_dforeign df ->
  lift (coq_Foreign ftype m.brand_model_relation)
    (fdtyping.foreign_data_typing_infer df)
