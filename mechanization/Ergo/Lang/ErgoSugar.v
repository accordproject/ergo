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
Require Import Ergo.Common.Utils.JNames.
Require Import Ergo.Ergo.Lang.ErgoBase.
Require Import Ergo.Ergo.Lang.Ergo.
Require Import Ergo.Backend.ErgoBackend.

Section ErgoSugar.
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition JDot (s:string) (e:ergo_expr) : ergo_expr :=
    JUnaryOp (ErgoOps.Unary.opdot s) (JUnaryOp ErgoOps.Unary.opunbrand e).

  (** [return expr] is a no-op at the moment *)
  Definition mk_result e1 e2 :=
    JBinaryOp ErgoOps.Binary.oprecconcat
              (JUnaryOp (ErgoOps.Unary.oprec "response") e1)
              (JUnaryOp (ErgoOps.Unary.oprec "state") e2).

  (** [return expr] is a no-op at the moment *)
  Definition JReturn e1 :=
    mk_result e1 JThisState.

  Definition JReturnSetState e1 e2 :=
    mk_result e1 e2.
  
  Definition JNewSugar pname cname el :ergo_expr :=
    JNew (mkClassRef pname cname) el.

  Definition JThrowSugar pname cname el : ergo_expr :=
    JThrow (mkClassRef pname cname) el.

  Definition JThrowErgoCompilerError (msg:string) : ergo_expr :=
    (JThrowSugar (Some "org.ergo")
                 "Error"
                 (("error", JConst (ErgoData.dstring msg))::nil))%string.

End ErgoSugar.

