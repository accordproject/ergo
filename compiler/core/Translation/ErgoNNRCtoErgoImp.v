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
  End Correctness.
End ErgoNNRCtoErgoImp.
