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

(* Provenance and location *)

Require Import String.
Require Import ZArith.
Require Import ErgoSpec.Backend.QLib.

Section Provenance.
  Record location_point :=
    mkLocationPoint {
        offset: Z;
        line : Z;
        column : Z;
      }.
  Record location :=
    mkLocation {
        loc_file: string;
        loc_start: location_point;
        loc_end: location_point;
      }.
  Definition dummy_location : location :=
    let dummy_location_point := mkLocationPoint (-1) (-1) (-1) in
    mkLocation "" dummy_location_point dummy_location_point.

  (* Provenance *)
  Inductive provenance :=
  | ProvFunc : location -> string -> provenance   (**r Compiled from function *)
  | ProvClause : location -> string -> provenance (**r Compiled from clause *)
  | ProvThisContract : location -> provenance     (**r Compiled from [contract] *)
  | ProvThisClause : location -> provenance       (**r Compiled from [clause] *)
  | ProvThisState : location -> provenance        (**r Compiled from [state] *)
  | ProvLoc : location -> provenance              (**r Compiled from others *)
  .

  Definition dummy_provenance : provenance :=
    ProvLoc dummy_location.

  Definition loc_of_provenance prov : location :=
    match prov with
    | ProvFunc loc _ => loc
    | ProvClause loc _ => loc
    | ProvThisContract loc => loc
    | ProvThisClause loc => loc
    | ProvThisState loc => loc
    | ProvLoc loc => loc
    end.

  Definition is_contract prov : bool :=
    match prov with
    | ProvThisContract loc => true
    | _ => false
    end.
  Definition is_clause prov : bool :=
    match prov with
    | ProvThisClause loc => true
    | _ => false
    end.
  Definition is_state prov : bool :=
    match prov with
    | ProvThisState loc => true
    | _ => false
    end.
    
  Definition string_of_location_point (lp : location_point) : string :=
    (toString lp.(line)) ++ ":" ++ (toString lp.(column)).

  Definition string_of_location (loc : location) : string :=
    let f := loc.(loc_file) in
    let file :=
        if string_dec f ""%string
        then ""%string
        else (f ++ " ")%string
    in
    file ++
         (string_of_location_point loc.(loc_start)) ++ "-" ++
         (string_of_location_point loc.(loc_end)).

  Definition string_of_location_no_file (loc : location) : string :=
    let file := ""%string
    in
    file ++
         (string_of_location_point loc.(loc_start)) ++ "-" ++
         (string_of_location_point loc.(loc_end)).

End Provenance.
