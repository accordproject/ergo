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

(** Translates ErgoNNRC to ErgoImp *)

Require Import String.
Require Import List.

Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Driver.CompDriver.
Require Import Qcert.Driver.CompCorrectness.
Require Import ErgoSpec.Version.
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.ErgoImp.Lang.ErgoImp.
Require Import ErgoSpec.Backend.QLib.

Section ErgoNNRCtoErgoImp.
  Local Open Scope list_scope.

  Context {bm:brand_model}.

  Section Translation.
    (** Single function *)
    Definition ergo_nnrc_function_to_imp
               (globals:list string)
               (fbody:ergo_nnrc_lambda) : ergo_imp_lambda :=
      QcertCodeGen.nnrc_expr_to_imp_ejson_function globals fbody.(lambdan_body).

    (** Function table *)
    Definition ergo_nnrc_function_table_to_imp
               (globals:list string)
               (ft:ergo_nnrc_function_table) : ergo_imp_function_table :=
      Imp.ImpLib (map (fun xy => (fst xy, ergo_nnrc_function_to_imp globals (snd xy))) ft.(function_tablen_funs)).

    (** Declaration *)
    Definition ergo_nnrc_declaration_to_imp
               (globals:list string)    (* globally known variables -- avoid list *)
               (s : ergo_nnrc_declaration)   (* statement to translate *)
      : ergo_imp_declaration
      :=
        match s with
        | DNFunc fname fbody => DIFunc fname (ergo_nnrc_function_to_imp globals fbody)
        | DNFuncTable cname ft => DIFuncTable cname (ergo_nnrc_function_table_to_imp globals ft)
        end.

    Definition ergo_nnrc_declarations_to_imp (sl : list ergo_nnrc_declaration) : list ergo_imp_declaration
      := map (ergo_nnrc_declaration_to_imp (* XXX globals *) nil) sl.

    (** Module *)
    Definition ergo_nnrc_module_to_imp (m : ergo_nnrc_module) : ergo_imp_module :=
      mkModuleI
        m.(modulen_provenance)
        m.(modulen_namespace)
        (ergo_nnrc_declarations_to_imp m.(modulen_declarations)).

  End Translation.

  Section Correctness.
    Definition same_result (r1 r2:eresult qcert_data) :=
      match r1, r2 with
      (* Either both successful with the same data *)
      | Success _ _ d1, Success _ _ d2 => d1 = d2
      (* Or both fail with any error *)
      | Failure _ _ e1, Failure _ _ e2 => True
      (* Otherwise the result is different *)
      | _, _ => False
      end.

    Notation "r1 ≡ r2" := (same_result r1 r2) (at level 90).

    Lemma ergo_function_lookup_correct s l:
      ergo_imp_declaration_lookup_function s (ergo_nnrc_declarations_to_imp l)
      = lift (ergo_nnrc_function_to_imp nil) (ergo_nnrc_declaration_lookup_function s l).
    Proof.
      induction l; intros; try reflexivity; simpl.
      destruct a; simpl; try assumption.
      destruct (string_dec s0 s); try assumption; subst.
      reflexivity.
    Qed.

    Lemma ergo_function_table_lookup_correct s l:
      ergo_imp_declaration_lookup_table s (ergo_nnrc_declarations_to_imp l)
      = lift (ergo_nnrc_function_table_to_imp nil) (ergo_nnrc_declaration_lookup_table s l).
    Proof.
      induction l; intros; try reflexivity; simpl.
      destruct a; simpl; try assumption.
      destruct (string_dec s0 s); try assumption; subst.
      reflexivity.
    Qed.
      
    Lemma ergo_function_in_function_table_lookup_correct s l :
      lift
        (ergo_nnrc_function_to_imp nil)
        (lookup string_dec l s) =
      (lookup string_dec
              (map (fun xy : string * ergo_nnrc_lambda => (fst xy, ergo_nnrc_function_to_imp nil (snd xy)))
                   l) s).
    Proof.
      induction l; intros; try reflexivity; simpl.
      destruct a; simpl in *.
      destruct (string_dec s s0); try reflexivity.
      rewrite IHl.
      reflexivity.
    Qed.

    Lemma ergo_nnrc_lambda_to_imp_correct (f:ergo_nnrc_lambda) :
      forall params: list (string * qcert_data),
        ergo_nnrc_lambda_eval f params ≡ ergo_imp_lambda_eval (ergo_nnrc_function_to_imp nil f) params.
    Proof.
      intros.
      unfold ergo_nnrc_lambda_eval.
      unfold ergo_imp_lambda_eval.
      unfold CompEval.eval_nnrc.
      unfold CompEval.h.
      unfold ergo_nnrc_function_to_imp.
      unfold QcertCodeGen.nnrc_expr_to_imp_ejson_function.
      rewrite (@eval_nnrc_to_imp_correct _ _ _ _ _ bm).
      unfold CompEval.h.
      unfold nnrc_expr_to_imp_ejson_function.
      assert (
          (@lift (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
          (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime))
          (@DataToEJson.ejson_to_data QcertData.enhanced_foreign_runtime QcertEJson.enhanced_foreign_ejson
             QcertDataToEJson.enhanced_foreign_to_ejson)
          (@ImpEJsonEval.imp_ejson_function_eval QcertEJson.enhanced_foreign_ejson
             (@ForeignDataToEJson.foreign_to_ejson_runtime QcertData.enhanced_foreign_runtime
                QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson)
             (@brand_relation_brands (@brand_model_relation QcertType.enhanced_foreign_type bm))
             (@ImpDatatoImpEJson.imp_data_function_to_imp_ejson QcertData.enhanced_foreign_runtime
                QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                (@ForeignDataToEJson.foreign_to_ejson_runtime QcertData.enhanced_foreign_runtime
                   QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson)
                QcertDataToEJson.enhanced_foreign_to_ejson_runtime
                (@CompEval.h QcertType.enhanced_foreign_type bm)
                (@NNRSimptoImpData.nnrs_imp_to_imp_data_function QcertData.enhanced_foreign_runtime
                   (@nnrs_to_nnrs_imp QcertData.enhanced_foreign_runtime
                      (@nnrc_to_nnrs QcertData.enhanced_foreign_runtime (@nil string) (@lambdan_body bm f)))))
             (@EJson.ejobject QcertEJson.enhanced_foreign_ejson
                (@rec_sort string ODT_string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                   (@map (prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)))
                      (prod string (@EJson.ejson QcertEJson.enhanced_foreign_ejson))
                      (fun xy : prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) =>
                       @pair string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                         (key_encode
                            (@fst string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy))
                         (@DataToEJson.data_to_ejson QcertData.enhanced_foreign_runtime
                            QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                            (@snd string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy)))
                      params)))))
          = (@lift (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
          (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime))
          (@DataToEJson.ejson_to_data QcertData.enhanced_foreign_runtime QcertEJson.enhanced_foreign_ejson
             QcertDataToEJson.enhanced_foreign_to_ejson)
          (@ImpEJsonEval.imp_ejson_function_eval QcertEJson.enhanced_foreign_ejson
             QcertEJson.enhanced_foreign_ejson_runtime
             (@brand_relation_brands (@brand_model_relation QcertType.enhanced_foreign_type bm))
             (@ImpDatatoImpEJson.imp_data_function_to_imp_ejson QcertData.enhanced_foreign_runtime
                QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                (@ForeignDataToEJson.foreign_to_ejson_runtime QcertData.enhanced_foreign_runtime
                   QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson)
                QcertDataToEJson.enhanced_foreign_to_ejson_runtime
                (@CompEval.h QcertType.enhanced_foreign_type bm)
                (@NNRSimptoImpData.nnrs_imp_to_imp_data_function QcertData.enhanced_foreign_runtime
                   (@nnrs_to_nnrs_imp QcertData.enhanced_foreign_runtime
                      (@nnrc_to_nnrs QcertData.enhanced_foreign_runtime (@nil string) (@lambdan_body bm f)))))
             (@EJson.ejobject QcertEJson.enhanced_foreign_ejson
                (@rec_sort string ODT_string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                   (@map (prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)))
                      (prod string (@EJson.ejson QcertEJson.enhanced_foreign_ejson))
                      (fun xy : prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) =>
                       @pair string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                         (key_encode
                            (@fst string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy))
                         (@DataToEJson.data_to_ejson QcertData.enhanced_foreign_runtime
                            QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                            (@snd string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy)))
                      params)))))
        ) by reflexivity.
      rewrite H; clear H.
      destruct (@lift (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
          (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime))
          (@DataToEJson.ejson_to_data QcertData.enhanced_foreign_runtime QcertEJson.enhanced_foreign_ejson
             QcertDataToEJson.enhanced_foreign_to_ejson)
          (@ImpEJsonEval.imp_ejson_function_eval QcertEJson.enhanced_foreign_ejson
             QcertEJson.enhanced_foreign_ejson_runtime
             (@brand_relation_brands (@brand_model_relation QcertType.enhanced_foreign_type bm))
             (@ImpDatatoImpEJson.imp_data_function_to_imp_ejson QcertData.enhanced_foreign_runtime
                QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                (@ForeignDataToEJson.foreign_to_ejson_runtime QcertData.enhanced_foreign_runtime
                   QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson)
                QcertDataToEJson.enhanced_foreign_to_ejson_runtime
                (@CompEval.h QcertType.enhanced_foreign_type bm)
                (@NNRSimptoImpData.nnrs_imp_to_imp_data_function QcertData.enhanced_foreign_runtime
                   (@nnrs_to_nnrs_imp QcertData.enhanced_foreign_runtime
                      (@nnrc_to_nnrs QcertData.enhanced_foreign_runtime (@nil string) (@lambdan_body bm f)))))
             (@EJson.ejobject QcertEJson.enhanced_foreign_ejson
                (@rec_sort string ODT_string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                   (@map (prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)))
                      (prod string (@EJson.ejson QcertEJson.enhanced_foreign_ejson))
                      (fun xy : prod string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) =>
                       @pair string (@EJson.ejson QcertEJson.enhanced_foreign_ejson)
                         (key_encode
                            (@fst string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy))
                         (@DataToEJson.data_to_ejson QcertData.enhanced_foreign_runtime
                            QcertEJson.enhanced_foreign_ejson QcertDataToEJson.enhanced_foreign_to_ejson
                            (@snd string (@data (@foreign_runtime_data QcertData.enhanced_foreign_runtime)) xy)))
                      params))))); simpl; auto.
    Qed.

    (** Main theorem of correctness for ErgoNNRC to ErgoImp translation.

     It states that invoking a contract on ErgoNNRC yields the same
     result (same successful evaluation or same error) as invoking the
     same clause of that contract after it has been translated to
     ErgoImp *)
    Theorem ergo_nnrc_to_imp_correct (m : ergo_nnrc_module) :
      forall callname : (option string * string),
      forall params: list (string * qcert_data),
        ergo_nnrc_invoke m callname params ≡ ergo_imp_invoke (ergo_nnrc_module_to_imp m) callname params.
    Proof.
      intros.
      destruct callname.
      destruct o; simpl.
      (* Proof for contract invoke *)
      - rewrite ergo_function_table_lookup_correct; simpl.
        destruct (ergo_nnrc_declaration_lookup_table s (modulen_declarations m));
          try reflexivity; simpl.
        unfold ergo_nnrc_function_table_eval.
        rewrite <- ergo_function_in_function_table_lookup_correct.
        destruct (lookup string_dec (function_tablen_funs e) s);
          try reflexivity; simpl.
        apply ergo_nnrc_lambda_to_imp_correct.
      (* Proof for function invoke *)
      - rewrite ergo_function_lookup_correct; simpl.
        destruct (ergo_nnrc_declaration_lookup_function s (modulen_declarations m));
          try reflexivity; simpl.
        apply ergo_nnrc_lambda_to_imp_correct.
    Qed.

  End Correctness.
End ErgoNNRCtoErgoImp.
