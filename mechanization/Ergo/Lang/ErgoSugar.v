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
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Pattern.EPattern.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoSugar.
  Context {A:Set}. (* Type for annotations *)
  
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition EDot (a:A) (s:string) (e:rergo_expr) : rergo_expr :=
    EUnaryOp a
             (ErgoOps.Unary.opdot s)
             (EUnaryOp a ErgoOps.Unary.opunbrand e).

  Definition SReturnEmpty (a:A) : rergo_stmt := SReturn a (EConst a dunit).

  Definition EFunReturnEmpty (a:A) : rergo_expr := EConst a dunit.

  Definition EOptionalDot (a:A) (pname:string) (e:rergo_expr) :=
    EMatch a
           e
           ((CaseLetOption "$option" None,
             EUnaryOp a (OpDot pname) (EVar a "$option")) :: nil)
           (EConst a dnone).

  Definition EOptionalDefault (a:A) (e1 e2:rergo_expr) :=
    EMatch a e1
           ((CaseLetOption "$option" None, EVar a "$option") :: nil)
           e2.

End ErgoSugar.
