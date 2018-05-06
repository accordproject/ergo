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
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoSugar.
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition EDot (s:string) (e:ergo_expr) : ergo_expr :=
    EUnaryOp (ErgoOps.Unary.opdot s) (EUnaryOp ErgoOps.Unary.opunbrand e).

  (** [return expr] is a no-op at the moment *)
  Definition mk_result e1 e2 e3 : ergo_expr :=
    ERecord (("response", e1)
               :: ("state", e2)
               :: ("emit", e3)
               :: nil)%string.

  Definition set_state e1 e2 : ergo_expr :=
    ELet "lstate" None e1 e2.

  Definition push_emit e1 e2 : ergo_expr :=
    ELet "lemit" None
         (EBinaryOp OpBagUnion
                    e1
                    (EVar "lemit"))
         e2.
  
  Definition ENewSugar pname cname el : ergo_expr :=
    ENew (mkClassRef pname cname) el.

  Definition EThrowSugar pname cname el : ergo_expr :=
    EThrow (mkClassRef pname cname) el.

  Definition EThrowErgoCompilerError (msg:string) : ergo_expr :=
    (EThrowSugar (Some "org.ergo")
                 "Error"
                 (("error", EConst (ErgoData.dstring msg))::nil))%string.

  Definition default_return := EConst (ErgoData.dunit).
  Definition default_set_state := EThisState.
  Definition default_emit := EConst (ErgoData.dcoll nil).
  
  Definition EReturn (e1 e2 e3: option ergo_expr) :=
    let e1 :=
        match e1 with
        | None => default_return
        | Some e => e
        end
    in
    let e2 :=
        match e2 with
        | None => default_set_state
        | Some e => e
        end
    in
    let e3 :=
        match e3  with
        | None => default_emit
        | Some e => e
        end
    in
    mk_result e1 e2 e3.
  
End ErgoSugar.

