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

(** * Abstract Syntax *)

Require Import String.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoNameResolve.

  (** Resolve names in expressions *)
  Fixpoint ergo_name_resolve
           (ctxt:context) (e:ergo_expr) : ergo_expr :=
    match e with
    | JThisContract => JThisContract
    | JThisClause => JThisClause
    | JThisState => JThisState
    | JVar v => JVar v
    | JConst d => JConst d
    | JArray el => JArray (List.map (ergo_name_resolve ctxt) el)
    | JUnaryOp u e =>
      JUnaryOp u (ergo_name_resolve e)
    | JBinaryOp b e1 e2 =>
      JBinaryOp b
                (ergo_name_resolve e1)
                (ergo_name_resolve e2)
    | JIf e1 e2 e3 =>
      JIf (ergo_name_resolve e1)
          (ergo_name_resolve e2)
          (ergo_name_resolve e3)
    | JEnforce e1 None e3 =>
      JEnforce (ergo_name_resolve e1)
               None
               (ergo_name_resolve e3)
    | JEnforce e1 (Some e2) e3 =>
      JEnforce (ergo_name_resolve e1)
               (Some (ergo_name_resolve e2))
               (ergo_name_resolve e3)
    | JLet v None e1 e2 =>
      JLet v None
           (ergo_name_resolve e1)
           (ergo_name_resolve e2)
    | JLet v (Some t1) e1 e2 => (** XXX TYPE IS IGNORED AT THE MOMENT *)
      JLet v (Some (resolve_type_name ctxt t1))
           (ergo_name_resolve e1)
           (ergo_name_resolve e2)
    | JNew cr nil =>
      jsuccess
        (new_expr (brand_of_class_ref ctxt.(context_namespace) cr) (NNRCConst (drec nil)))
    | JNew cr ((s0,init)::rest) =>
      let init_rec : jresult nnrc :=
          jlift (NNRCUnop (OpRec s0)) (ergo_expr_to_calculus ctxt init)
      in
      let proc_one (acc:jresult nnrc) (att:string * ergo_expr) : jresult nnrc :=
          let attname := fst att in
          let e := ergo_expr_to_calculus ctxt (snd att) in
          jlift2 (NNRCBinop OpRecConcat)
                 (jlift (NNRCUnop (OpRec attname)) e) acc
      in
      jlift (new_expr (brand_of_class_ref ctxt.(context_namespace) cr)) (fold_left proc_one rest init_rec)
    | JRecord nil =>
      jsuccess
        (NNRCConst (drec nil))
    | JRecord ((s0,init)::rest) =>
      let init_rec : jresult nnrc :=
          jlift (NNRCUnop (OpRec s0)) (ergo_expr_to_calculus ctxt init)
      in
      let proc_one (acc:jresult nnrc) (att:string * ergo_expr) : jresult nnrc :=
          let attname := fst att in
          let e := ergo_expr_to_calculus ctxt (snd att) in
          jlift2 (NNRCBinop OpRecConcat)
                 (jlift (NNRCUnop (OpRec attname)) e) acc
      in
      fold_left proc_one rest init_rec
    | JThrow cr nil =>
      jsuccess (new_expr (brand_of_class_ref ctxt.(context_namespace) cr) (NNRCConst (drec nil)))
    | JThrow cr ((s0,init)::rest) =>
      let init_rec : jresult nnrc :=
          jlift (NNRCUnop (OpRec s0)) (ergo_expr_to_calculus ctxt init)
      in
      let proc_one (acc:jresult nnrc) (att:string * ergo_expr) : jresult nnrc :=
          let attname := fst att in
          let e := ergo_expr_to_calculus ctxt (snd att) in
          jlift2 (NNRCBinop OpRecConcat)
                 (jlift (NNRCUnop (OpRec attname)) e)
                 acc
      in
      jlift (new_expr (brand_of_class_ref ctxt.(context_namespace) cr)) (fold_left proc_one rest init_rec)
    | JFunCall fname el =>
      let init_el := jsuccess nil in
      let proc_one (e:ergo_expr) (acc:jresult (list ergoc_expr)) : jresult (list ergoc_expr) :=
          jlift2
            cons
            (ergo_expr_to_calculus ctxt e)
            acc
      in
      jolift (lookup_call ctxt.(context_table) fname) (fold_right proc_one init_el el)
    | JMatch e0 ecases edefault =>
      let ec0 := ergo_expr_to_calculus ctxt e0 in
      let eccases :=
          let proc_one acc ecase :=
              jolift
                (fun acc =>
                   jlift (fun x => (fst ecase, x)::acc)
                         (ergo_expr_to_calculus ctxt (snd ecase))) acc
          in
          fold_left proc_one ecases (jsuccess nil)
      in
      let ecdefault := ergo_expr_to_calculus ctxt edefault in
      jolift
        (fun ec0 =>
           jolift
             (fun eccases =>
                jolift
                  (fun ecdefault =>
                     let v0 := fresh_in_match eccases ecdefault in
                     let proc_one_case
                           (acc:jresult ergoc_expr)
                           (ecase:match_case * ergoc_expr)
                         : jresult ergoc_expr :=
                         match fst ecase with
                         | (Some v, CaseValue d) =>
                           jlift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (NNRCLet v
                                                (NNRCVar v0)
                                                (snd ecase))
                                       acc) acc
                         | (None, CaseValue d) =>
                           jlift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (snd ecase)
                                       acc) acc
                         | (Some v, CaseType brand) =>
                           jlift (fun acc =>
                                    let v2 := fresh_in_case acc in
                                    NNRCEither
                                      (NNRCUnop (OpCast (brand::nil)) (NNRCVar v0))
                                      v (snd ecase)
                                      v2 acc
                                 ) acc
                         | (None, CaseType brand) =>
                           jlift (fun acc =>
                                    let v1 := fresh_in_case (snd ecase) in
                                    let v2 := fresh_in_case acc in
                                    NNRCEither
                                      (NNRCUnop (OpCast (brand::nil)) (NNRCVar v0))
                                      v1 (snd ecase)
                                      v2 acc
                                 ) acc
                         end
                     in
                     let eccases_folded :=
                         fold_left proc_one_case eccases (jsuccess ecdefault)
                     in
                     jlift (NNRCLet v0 ec0) eccases_folded)
                  ecdefault) eccases) ec0
    | JFor v e1 None e2 =>
      jlift2 (NNRCFor v)
              (ergo_expr_to_calculus ctxt e1)
              (ergo_expr_to_calculus ctxt e2)
    | JFor v e1 (Some econd) e2 =>
      jlift3 (fun e1 econd e3 =>
                NNRCUnop OpFlatten
                         (NNRCFor v
                                  e1
                                  (NNRCIf econd
                                          (NNRCUnop OpBag e3)
                                          (NNRCConst (dcoll nil)))))
             (ergo_expr_to_calculus ctxt e1)
             (ergo_expr_to_calculus ctxt econd)
             (ergo_expr_to_calculus ctxt e2)
    end.

