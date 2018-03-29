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

(** Jura is a language for expressing contract logic. *)

(** * Syntactic sugar *)

Require Import String.
Require Import List.
Require Import Jura.Common.Utils.JNames.
Require Import Jura.Jura.Lang.JuraBase.
Require Import Jura.Jura.Lang.Jura.
Require Import Jura.Backend.JuraBackend.

Section JuraSugar.
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition JDot (s:string) (e:jura_expr) : jura_expr :=
    JUnaryOp (JuraOps.Unary.opdot s) (JUnaryOp JuraOps.Unary.opunbrand e).

  (** [return expr] is a no-op at the moment *)
  (* XXX This will have to be revised/fixed *)
  Definition JReturn (e:jura_expr) : jura_expr := e.

  Definition JNewSugar pname cname el :jura_expr :=
    JNew (mkClassRef pname cname) el.

  Definition JThrowSugar pname cname el : jura_expr :=
    JThrow (mkClassRef pname cname) el.

  Definition JThrowJuraCompilerError (msg:string) : jura_expr :=
    (JThrowSugar (Some "org.jura")
                 "Error"
                 (("error", JConst (JuraData.dstring msg))::nil))%string.

End JuraSugar.

