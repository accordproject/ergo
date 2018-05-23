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
Require Import List.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.Ergo.

Section ErgoNameResolve.

  (** Resolve names in expressions *)
  Fixpoint ergo_name_resolve (ctxt:list cto_declaration) (e:ergo_expr) : ergo_expr :=
    match e with
    | EThisContract => esuccess EThisContract
    | EThisClause => esuccess EThisClause
    | EThisState => esuccess EThisState
    | EVar v => esuccess (EVar v)
    | EConst d => esuccess (EConst d)
    | EArray el =>
      let init_el := esuccess nil in
      let proc_one (acc:eresult (list ergo_expr)) (e:ergo_expr) : eresult (list ergo_expr) :=
          elift2
            cons
            (ergo_name_resolve ctxt e)
            acc
      in
      elift EArray (fold_left proc_one el init_el)
    | EUnaryOp u e =>
      elift (EUnaryOp u)
            (ergo_name_resolve ctxt e)
    | EBinaryOp b e1 e2 =>
      elift2 (EBinaryOp b)
             (ergo_name_resolve ctxt e1)
             (ergo_name_resolve ctxt e2)
    | EIf e1 e2 e3 =>
      elift3 EIf
        (ergo_name_resolve ctxt e1)
        (ergo_name_resolve ctxt e2)
        (ergo_name_resolve ctxt e3)
    | EEnforce e1 None e3 =>
      elift3 EEnforce
        (ergo_name_resolve ctxt e1)
        (esuccess None)
        (ergo_name_resolve ctxt e3)
    | EEnforce e1 (Some e2) e3 =>
      elift3 EEnforce
        (ergo_name_resolve ctxt e1)
        (ergo_name_resolve ctxt e3)
        (ergo_name_resolve ctxt e2)
    | ELet v None e1 e2 =>
      elift2 (ELet v None)
             (ergo_name_resolve ctxt e1)
             (ergo_name_resolve ctxt e2)
    | ELet v (Some t1) e1 e2 =>
      elift2 (ELet v (Some t1))
              (ergo_name_resolve ctxt e1)
              (ergo_name_resolve ctxt e2)
    | ENew cr nil =>
      esuccess
        (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr) (NNRCConst (drec nil)))
    | ENew cr ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergo_name_resolve ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergo_name_resolve ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 (elift (NNRCUnop (OpRec attname)) e) acc
      in
      elift (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr)) (fold_left proc_one rest init_rec)
    | ERecord nil =>
      esuccess
        (NNRCConst (drec nil))
    | ERecord ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergo_name_resolve ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergo_name_resolve ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 (elift (NNRCUnop (OpRec attname)) e) acc
      in
      fold_left proc_one rest init_rec
    | EThrow cr nil =>
      esuccess (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr) (NNRCConst (drec nil)))
    | EThrow cr ((s0,init)::rest) =>
      let init_rec : eresult nnrc :=
          elift (NNRCUnop (OpRec s0)) (ergo_name_resolve ctxt init)
      in
      let proc_one (acc:eresult nnrc) (att:string * ergo_expr) : eresult nnrc :=
          let attname := fst att in
          let e := ergo_name_resolve ctxt (snd att) in
          elift2 (NNRCBinop OpRecConcat)
                 (elift (NNRCUnop (OpRec attname)) e)
                 acc
      in
      elift (new_expr (absolute_ref_of_class_ref ctxt.(comp_context_namespace) cr)) (fold_left proc_one rest init_rec)
    | ECall fname el =>
      let init_el := esuccess nil in
      let proc_one (e:ergo_expr) (acc:eresult (list ergoc_expr)) : eresult (list ergoc_expr) :=
          elift2
            cons
            (ergo_name_resolve ctxt e)
            acc
      in
      eolift (lookup_call ctxt.(comp_context_table) fname) (fold_right proc_one init_el el)
    | EMatch e0 ecases edefault =>
      let ec0 := ergo_name_resolve ctxt e0 in
      let eccases :=
          let proc_one acc ecase :=
              eolift
                (fun acc =>
                   elift (fun x => (fst ecase, x)::acc)
                         (ergo_name_resolve ctxt (snd ecase))) acc
          in
          fold_left proc_one ecases (esuccess nil)
      in
      let ecdefault := ergo_name_resolve ctxt edefault in
      eolift
        (fun ec0 =>
           eolift
             (fun eccases =>
                eolift
                  (fun ecdefault =>
                     let v0 := fresh_in_match eccases ecdefault in
                     let proc_one_case
                           (acc:eresult ergoc_expr)
                           (ecase:match_case * ergoc_expr)
                         : eresult ergoc_expr :=
                         match fst ecase with
                         | (Some v, CaseValue d) =>
                           elift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (NNRCLet v
                                                (NNRCVar v0)
                                                (snd ecase))
                                       acc) acc
                         | (None, CaseValue d) =>
                           elift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (snd ecase)
                                       acc) acc
                         | (Some v, CaseType brand) =>
                           elift (fun acc =>
                                    let v2 := fresh_in_case acc in
                                    NNRCEither
                                      (NNRCUnop (OpCast (brand::nil)) (NNRCVar v0))
                                      v (snd ecase)
                                      v2 acc
                                 ) acc
                         | (None, CaseType brand) =>
                           elift (fun acc =>
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
                         fold_left proc_one_case eccases (esuccess ecdefault)
                     in
                     elift (NNRCLet v0 ec0) eccases_folded)
                  ecdefault) eccases) ec0
    | EForeach foreachs None e2 =>
      let init_e := ergo_name_resolve ctxt e2 in
      let proc_one (acc:eresult nnrc) (foreach:string * ergo_expr) : eresult nnrc :=
          let v := fst foreach in
          let e := ergo_name_resolve ctxt (snd foreach) in
          elift2 (NNRCFor v)
                 e
                 acc
      in
      fold_left proc_one foreachs init_e
    | EForeach foreachs (Some econd) e2 =>
      let init_e :=
          elift2
            (fun econd e2 =>
               NNRCIf econd
                     (NNRCUnop OpBag e2)
                     (NNRCConst (dcoll nil)))
            (ergo_name_resolve ctxt econd)
            (ergo_name_resolve ctxt e2)
      in
      let proc_one (acc:eresult nnrc) (foreach:string * ergo_expr) : eresult nnrc :=
          let v := fst foreach in
          let e := ergo_name_resolve ctxt (snd foreach) in
          elift2 (NNRCFor v)
                 e
                 acc
      in
      elift (NNRCUnop OpFlatten)
            (fold_left proc_one foreachs init_e)
    end.
