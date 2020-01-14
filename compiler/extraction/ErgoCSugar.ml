open BinaryOperators
open BrandRelation
open Data
open Ergo
open ErgoC
open ErgoType
open Lift
open Names
open Provenance
open String0
open UnaryOperators

(** val mkResult :
    provenance -> (provenance, provenance, absolute_name) ergo_expr ->
    (provenance, provenance, absolute_name) ergo_expr -> (provenance,
    provenance, absolute_name) ergo_expr -> ergoc_expr **)

let mkResult prov e1 e2 e3 =
  ERecord (prov, ((this_response, e1) :: ((this_state, e2) :: ((this_emit,
    e3) :: []))))

(** val setState :
    provenance -> (provenance, provenance, absolute_name) ergo_expr ->
    (provenance, provenance, absolute_name) ergo_expr -> ergoc_expr **)

let setState prov e1 e2 =
  ELet (prov, local_state, None, e1, e2)

(** val thisThis : provenance -> ergoc_expr **)

let thisThis prov =
  EVar (prov, this_this)

(** val setStateDot :
    provenance -> char list -> brand -> (provenance, provenance, char list)
    ergo_expr -> (provenance, provenance, absolute_name) ergo_expr ->
    ergoc_expr **)

let setStateDot prov name tname e1 e2 =
  setState prov (EUnaryBuiltin (prov, (OpBrand (tname :: [])),
    (EBinaryBuiltin (prov, OpRecConcat, (EUnaryBuiltin (prov, OpUnbrand,
    (EVar (prov, local_state)))), (EUnaryBuiltin (prov, (OpRec name),
    e1)))))) e2

(** val thisContract : provenance -> ergoc_expr **)

let thisContract prov =
  let prov0 = ProvThisContract (loc_of_provenance prov) in
  EVar (prov0, this_contract)

(** val thisClause : provenance -> char list -> ergoc_expr **)

let thisClause prov clause_name =
  let prov0 = ProvThisClause (loc_of_provenance prov) in
  EUnaryBuiltin (prov0, (OpDot clause_name), (EUnaryBuiltin (prov0,
  OpUnbrand, (EVar (prov0, this_contract)))))

(** val thisState : provenance -> ergoc_expr **)

let thisState prov =
  let prov0 = ProvThisState (loc_of_provenance prov) in
  EVar (prov0, local_state)

(** val pushEmit :
    provenance -> (provenance, provenance, char list) ergo_expr ->
    (provenance, provenance, char list) ergo_expr -> ergoc_expr **)

let pushEmit prov e1 e2 =
  ELet (prov, local_emit, None, (EBinaryBuiltin (prov, OpBagUnion,
    (EUnaryBuiltin (prov, OpBag, e1)), (EVar (prov, local_emit)))), e2)

(** val coq_ESuccess : provenance -> ergoc_expr -> ergoc_expr **)

let coq_ESuccess prov e =
  EUnaryBuiltin (prov, OpLeft, e)

(** val coq_EFailure : provenance -> ergoc_expr -> ergoc_expr **)

let coq_EFailure prov e =
  EUnaryBuiltin (prov, OpRight, e)

(** val coq_ECallClause :
    provenance -> char list -> char list -> ergoc_expr list -> ergoc_expr **)

let coq_ECallClause prov coname clname el =
  let params =
    if string_dec clname clause_init_name
    then (thisContract prov) :: ((EConst (prov, Coq_dunit)) :: ((EVar (prov,
           local_emit)) :: el))
    else (thisContract prov) :: ((EVar (prov, local_state)) :: ((EVar (prov,
           local_emit)) :: el))
  in
  ECallFunInGroup (prov, coname, clname, params)

(** val coq_EReturn : provenance -> ergoc_expr -> ergoc_expr **)

let coq_EReturn prov e =
  coq_ESuccess prov
    (mkResult prov e (EVar (prov, local_state)) (EVar (prov, local_emit)))

(** val coq_EBindThis :
    provenance -> char list -> ergoc_expr -> (provenance, provenance,
    absolute_name) ergo_expr **)

let coq_EBindThis prov _ e =
  ELet (prov, this_this, None, (thisContract prov), e)

(** val coq_EWrapTop :
    provenance -> ergoc_expr -> (provenance, provenance, char list) ergo_expr **)

let coq_EWrapTop prov e =
  ELet (prov, local_state, None, (EVar (prov, this_state)), (ELet (prov,
    local_emit, None, (EVar (prov, this_emit)), e)))

(** val coq_EClauseAsFunction :
    provenance -> char list -> laergo_type -> laergo_type option ->
    laergo_type option -> laergo_type option -> (char list * (provenance,
    absolute_name) ergo_type) list -> ergoc_expr option ->
    char list * ergoc_function **)

let coq_EClauseAsFunction prov clname template emit state response params body =
  let emit_type = lift_default_emits_type prov emit in
  let state_type = lift_default_state_type prov state in
  let throw_type = default_throws_type prov in
  let output_type =
    match response with
    | Some response_type ->
      let success_type =
        mk_success_type prov response_type state_type emit_type
      in
      let error_type = mk_error_type prov throw_type in
      Some (mk_output_type prov success_type error_type)
    | None -> None
  in
  let params0 =
    if string_dec clname clause_init_name
    then (this_contract, template) :: ((this_state, (ErgoTypeUnit
           prov)) :: ((this_emit, (ErgoTypeArray (prov, (ErgoTypeNothing
           prov)))) :: params))
    else (this_contract, template) :: ((this_state,
           state_type) :: ((this_emit, (ErgoTypeArray (prov, (ErgoTypeNothing
           prov)))) :: params))
  in
  let wrapped_body =
    lift (coq_EWrapTop prov) (lift (coq_EBindThis prov clname) body)
  in
  (clname, { functionc_annot = prov; functionc_sig = { sigc_params = params0;
  sigc_output = output_type }; functionc_body = wrapped_body })
