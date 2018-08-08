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
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCSugar.
  Definition mkResult (prov:provenance) e1 e2 e3 : ergoc_expr :=
    ERecord prov
            ((this_response, e1)
               :: (this_state, e2)
               :: (this_emit, e3)
               :: nil).

  Definition setState (prov:provenance) e1 e2 : ergoc_expr :=
    ELet prov local_state None e1 e2.

  Definition thisContract (prov:provenance) : ergoc_expr :=
    let prov := ProvThisContract (loc_of_provenance prov) in
    EVar prov this_contract.

  Definition thisClause (prov:provenance) clause_name : ergoc_expr :=
    let prov := ProvThisClause (loc_of_provenance prov) in
    EUnaryOp prov
             (OpDot clause_name)
             (EUnaryOp prov OpUnbrand (EVar prov this_contract)).

  Definition thisState (prov:provenance) : ergoc_expr :=
    let prov := ProvThisState (loc_of_provenance prov) in
    EVar prov local_state.

  Definition pushEmit (prov:provenance) e1 e2 : ergoc_expr :=
    ELet prov local_emit None
         (EBinaryOp prov
                    OpBagUnion
                    (EUnaryOp prov OpBag e1)
                    (EVar prov local_emit))
         e2.

  Definition ESuccess (prov:provenance) (e:ergoc_expr) : ergoc_expr :=
    EUnaryOp prov OpLeft e.

  Definition EError (prov:provenance) (e:ergoc_expr) : ergoc_expr :=
    EUnaryOp prov OpRight e.

End ErgoCSugar.
