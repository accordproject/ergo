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
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Backend.ErgoBackend.

Section ErgoSugar.
  Context {A:Set}. (* For expression annotations *)
  Context {A':Set}. (* For type annotations *)
  
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition SReturnEmpty (a:A) : @rergo_stmt A A' := SReturn a (EConst a dunit).

  Definition EFunReturnEmpty (a:A) : @rergo_expr A A' := EConst a dunit.

  Definition EOptionalDot (a:A) (pname:string) (e:@rergo_expr A A') :=
    EMatch a
           e
           ((CaseLetOption a "$option" None,
             (ESome a
                    (EUnaryOperator a (EOpDot pname) (EVar a (None,"$option"%string))))) :: nil)
           (ENone a).

  Definition EOptionalDefault (a:A) (e1 e2:@rergo_expr A A') :=
    EMatch a e1
           ((CaseLetOption a "$option" None, EVar a (None,"$option"%string)) :: nil)
           e2.

End ErgoSugar.
