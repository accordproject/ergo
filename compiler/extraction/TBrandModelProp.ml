open Assoc
open BrandRelation
open ForeignType
open Lattice
open List0
open RType
open RTypeLattice
open String0
open TBrandContext
open TBrandModel

(** val brands_type_list :
    foreign_type -> brand_model -> brands -> rtype list **)

let brands_type_list ftype m b =
  flat_map (fun bb ->
    match lookup string_dec
            (brand_context_types ftype m.brand_model_relation
              m.brand_model_context) bb with
    | Some _UU03c4_ -> _UU03c4_ :: []
    | None -> []) b

(** val brands_type : foreign_type -> brand_model -> brands -> rtype **)

let brands_type ftype m b =
  fold_left (rtype_lattice ftype m.brand_model_relation).meet
    (brands_type_list ftype m b) (coq_Top ftype m.brand_model_relation)
