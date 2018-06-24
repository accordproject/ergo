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
  (** [expr.field] is a macro for unbranding followed by field access in a record *)
  Definition EDot (loc:location) (s:string) (e:ergo_expr) : ergo_expr :=
    mk_expr loc (EUnaryOp (ErgoOps.Unary.opdot s)
                          (mk_expr loc (EUnaryOp ErgoOps.Unary.opunbrand e))).

  (** [return expr] is a no-op at the moment *)
  Definition mk_result (loc:location) e1 e2 e3 : ergo_expr :=
    mk_expr loc
            (ERecord ((this_response, e1)
                        :: (this_state, e2)
                        :: (this_emit, e3)
                        :: nil)).

  Definition set_state (loc:location) e1 e2 : ergo_expr :=
    mk_expr loc
            (ELet local_state None e1 e2).

  Definition this_clause (loc:location) clause_name :=
    mk_expr loc
            (EUnaryOp (OpDot clause_name)
                      (mk_expr loc (EUnaryOp OpUnbrand (mk_expr loc EThisContract)))).

  Definition push_emit (loc:location) e1 e2 : ergo_expr :=
    mk_expr loc
            (ELet local_emit None
                  (mk_expr loc
                           (EBinaryOp OpBagUnion
                                      (mk_expr loc (EUnaryOp OpBag e1))
                                      (mk_expr loc (EVar local_emit))))
                  e2).

  Definition SThrowSugar (loc:location) pname cname el : ergo_stmt :=
    mk_stmt loc
            (SThrow (mk_expr loc (ENew (RelativeRef pname cname) el))).

  Definition SThrowErgoCompilerError (loc:location) (msg:string) : ergo_stmt :=
    SThrowSugar loc
                (Some "org.ergo"%string)
                "Error"%string
                (("error"%string, mk_expr loc
                                   (EConst (ErgoData.dstring msg)))::nil).

  Definition SReturnEmpty (loc:location) :=
    mk_stmt loc (SReturn (mk_expr loc (EConst dunit))).
  
  Definition SFunReturnEmpty (loc:location) :=
    mk_stmt loc (SFunReturn (mk_expr loc (EConst dunit))).

  Section Errors.
    Definition ESuccess (loc:location) (e:ergo_expr) : ergo_expr :=
      mk_expr loc (EUnaryOp OpLeft e).
      
    Definition EError (loc:location) (e:ergo_expr) : ergo_expr :=
      mk_expr loc (EUnaryOp OpRight e).

  End Errors.

  Section Optional.
    Definition EOptionalDot (loc:location) (pname:string) (e:ergo_expr) :=
      mk_expr loc
              (EMatch e
                      ((CaseLetOption "$option" None,
                        mk_expr loc (EUnaryOp (OpDot pname) (mk_expr loc (EVar "$option")))) :: nil)
                      (mk_expr loc (EConst dnone))).
    Definition EOptionalDefault (loc:location) (e1 e2:ergo_expr) :=
      mk_expr loc
              (EMatch e1
                      ((CaseLetOption "$option" None, mk_expr loc (EVar "$option")) :: nil)
                      e2).
  End Optional.

End ErgoSugar.
