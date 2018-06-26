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
  Section ParserSugar.
    Context {A:Set}. (* Type for annotations *)
  
    (** [expr.field] is a macro for unbranding followed by field access in a record *)
    Definition EDot (a:A) (s:string) (e:rergo_expr) : rergo_expr :=
      EUnaryOp a
               (ErgoOps.Unary.opdot s)
               (EUnaryOp a ErgoOps.Unary.opunbrand e).

    Definition SReturnEmpty (a:A) : rergo_stmt :=
      SReturn a (EConst a dunit).
  
    Definition SFunReturnEmpty (a:A) : rergo_stmt :=
      SFunReturn a (EConst a dunit).

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

    (*
    Definition SThrowSugar (loc:location) (ns:namespace_prefix) (ln:local_name) (el:list (string*laergo_expr)) : laergo_stmt :=
      SThrow loc (ENew loc (ns,ln) el).
*)

    (*
    Definition SThrowErgoCompilerError (a:A) (msg:string) : rergo_stmt :=
      SThrowSugar a
                  (Some "org.ergo"%string)
                  "Error"%string
                  (("error"%string, EConst a (ErgoData.dstring msg))::nil).
*)

  End ParserSugar.

  Section StmtSugar.
    (** [return expr] is a no-op at the moment *)
    Definition mk_result (loc:location) e1 e2 e3 : laergo_expr :=
      ERecord loc
              ((this_response, e1)
                 :: (this_state, e2)
                 :: (this_emit, e3)
                 :: nil).

    Definition set_state (loc:location) e1 e2 : laergo_expr :=
      ELet loc local_state None e1 e2.

    Definition this_clause (loc:location) clause_name : laergo_expr :=
      EUnaryOp loc
               (OpDot clause_name)
               (EUnaryOp loc OpUnbrand (EThisContract loc)).

    Definition push_emit (loc:location) e1 e2 : laergo_expr :=
      ELet loc local_emit None
           (EBinaryOp loc
                      OpBagUnion
                      (EUnaryOp loc OpBag e1)
                      (EVar loc local_emit))
           e2.

    Definition ESuccess (loc:location) (e:laergo_expr) : laergo_expr :=
      EUnaryOp loc OpLeft e.
      
    Definition EError (loc:location) (e:laergo_expr) : laergo_expr :=
      EUnaryOp loc OpRight e.

  End StmtSugar.

End ErgoSugar.
