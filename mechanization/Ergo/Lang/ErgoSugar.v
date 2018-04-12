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
  Definition mk_result e1 e2 :=
    EBinaryOp ErgoOps.Binary.oprecconcat
              (EUnaryOp (ErgoOps.Unary.oprec "response") e1)
              (EUnaryOp (ErgoOps.Unary.oprec "state") e2).

  (** [return expr] is a no-op at the moment *)
  Definition EReturn e1 :=
    mk_result e1 EThisState.

  Definition EReturnSetState e1 e2 :=
    mk_result e1 e2.
  
  Definition ENewSugar pname cname el :ergo_expr :=
    ENew (mkClassRef pname cname) el.

  Definition EThrowSugar pname cname el : ergo_expr :=
    EThrow (mkClassRef pname cname) el.

  Definition EThrowErgoCompilerError (msg:string) : ergo_expr :=
    (EThrowSugar (Some "org.ergo")
                 "Error"
                 (("error", EConst (ErgoData.dstring msg))::nil))%string.

End ErgoSugar.

