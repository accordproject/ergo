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
Require Import Qcert.NNRC.NNRCRuntime.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoCalculusSugar.
  Open Scope string.

  (** Fresh variables *)
  Definition fresh_in_match {A} (eccases:list (A * ergoc_expr)) (ecdefault:ergoc_expr) :=
    fresh_var
      "$match"
      (List.app
         (List.concat
            (List.map (fun eccase => nnrc_free_vars (snd eccase)) eccases))
         (nnrc_free_vars ecdefault)).

  Definition fresh_in_case (pattern_expr:ergoc_expr) (else_expr:ergoc_expr) : string :=
    fresh_var "$case"
              (List.app (nnrc_free_vars pattern_expr) (nnrc_free_vars else_expr)).

  Definition fresh_in_lift_error (e:ergoc_expr) :=
    fresh_var2 "$lifte" "$lifte"
               (nnrc_free_vars e).
  Definition fresh_in_lift_optional (e:ergoc_expr) :=
    fresh_var2 "$lifto" "$lifto"
               (nnrc_free_vars e).

  (** New Array *)
  Definition new_array (el:list ergoc_expr) : ergoc_expr :=
    match el with
    | nil => NNRCConst (dcoll nil)
    | e1::erest =>
      fold_left (fun acc e => NNRCBinop OpBagUnion (NNRCUnop OpBag e) acc) erest (NNRCUnop OpBag e1)
    end.

  (** [new Concept{ field1: expr1, ... fieldn: exprn }] creates a record and brands it with the concept name *)
  Definition new_expr (brand:string) (struct_expr:ergoc_expr) : ergoc_expr :=
    NNRCUnop (OpBrand (brand :: nil)) struct_expr.

End ErgoCalculusSugar.

