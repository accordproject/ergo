(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** Ergo is a language for expressing contract logic. *)

(** * Syntactic sugar *)

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.

Section ErgoCSugar.
  Definition mkResult (prov:provenance) e1 e2 e3 : ergoc_expr :=
    ERecord prov
            ((this_response, e1)
               :: (this_state, e2)
               :: (this_emit, e3)
               :: nil).

  Definition setState (prov:provenance) e1 e2 : ergoc_expr :=
    ELet prov local_state None e1 e2.

  Definition thisThis (prov:provenance) : ergoc_expr :=
    EVar prov this_this.

  Definition thisContract (prov:provenance) : ergoc_expr :=
    let prov := ProvThisContract (loc_of_provenance prov) in
    EVar prov this_contract.

  Definition thisClause (prov:provenance) clause_name : ergoc_expr :=
    let prov := ProvThisClause (loc_of_provenance prov) in
    EUnaryBuiltin prov
                  (OpDot clause_name)
                  (EUnaryBuiltin prov OpUnbrand (EVar prov this_contract)).

  Definition thisState (prov:provenance) : ergoc_expr :=
    let prov := ProvThisState (loc_of_provenance prov) in
    EVar prov local_state.

  Definition pushEmit (prov:provenance) e1 e2 : ergoc_expr :=
    ELet prov local_emit None
         (EBinaryBuiltin prov
                         OpBagUnion
                         (EUnaryBuiltin prov OpBag e1)
                         (EVar prov local_emit))
         e2.

  Definition ESuccess (prov:provenance) (e:ergoc_expr) : ergoc_expr :=
    EUnaryBuiltin prov OpLeft e.

  Definition EFailure (prov:provenance) (e:ergoc_expr) : ergoc_expr :=
    EUnaryBuiltin prov OpRight e.

  Definition ECallClause (prov:provenance) (coname clname:string) (el:list ergoc_expr) : ergoc_expr :=
    let params :=
        if string_dec clname clause_init_name
        then
          ((thisContract prov)
             ::(EConst prov dunit)
             ::(EVar prov local_emit)
             ::el)
        else
          ((thisContract prov)
             ::(EVar prov local_state)
             ::(EVar prov local_emit)
             ::el)
    in
    ECallFunInGroup
      prov
      coname
      clname
      params.

  Definition EReturn (prov:provenance) (e:ergoc_expr) : ergoc_expr :=
    ESuccess prov
             (mkResult
                prov
                e
                (EVar prov local_state)
                (EVar prov local_emit)).

  Definition EBindThis (prov:provenance) (clname:string) (e:ergoc_expr) :=
    ELet prov
         this_this
         None
         (thisContract prov)
         e.

  Definition EWrapTop (prov:provenance) (e:ergoc_expr) :=
    ELet prov
         local_state
         None
         (EVar prov this_state)
         (ELet prov local_emit None
               (EVar prov this_emit)
               e).

  Definition EClauseAsFunction
             (prov:provenance)
             (clname:string)
             (template: laergo_type)
             (emit:option laergo_type)
             (state:option laergo_type)
             (response:option laergo_type)
             (params:list (string * ergo_type))
             (body:option ergoc_expr) :=
    let emit_type := lift_default_emits_type prov emit in
    let state_type :=  lift_default_state_type prov state in
    let throw_type := default_throws_type prov in
    let output_type :=
        match response with
        | None => None
        | Some response_type =>
          let success_type := mk_success_type prov response_type state_type emit_type in
          let error_type := mk_error_type prov throw_type in
          Some (mk_output_type prov success_type error_type)
        end
    in
    let params :=
        if string_dec clname clause_init_name
        then
          ((this_contract, template)
             ::(this_state, ErgoTypeUnit prov)
             ::(this_emit, ErgoTypeArray prov (ErgoTypeNothing prov))
             ::params)
        else
          ((this_contract, template)
             ::(this_state, state_type)
             ::(this_emit, ErgoTypeArray prov (ErgoTypeNothing prov))
             ::params)
    in
    let wrapped_body := lift (EWrapTop prov) (lift (EBindThis prov clname) body) in
    (* let wrapped_body := lift (EWrapTop prov) (body) in *)
    (clname,
     mkFuncC
       prov
       (mkSigC
          params
          output_type)
       wrapped_body).

End ErgoCSugar.
