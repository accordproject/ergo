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

(** ErgoImp is an IL with function tables where the body of those functions is written as Imp expressions. It is the main interface with Q*cert for code-generation. *)

(** * Abstract Syntax *)

Require Import String.
Require Import List.
Require Import Qcert.Driver.CompEval.
Require Import ErgoSpec.Backend.QLib.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.

Section ErgoImp.
  Section Syntax.
    Context {m : brand_model}.

    (** Function *)
    Definition ergo_imp_lambda := QcertCodeGen.imp_ejson_function.

    (** Function table *)
    Definition ergo_imp_function_table := QcertCodeGen.imp_ejson_lib.

    (** Declaration *)
    Inductive ergo_imp_declaration :=
    | DIFunc : string -> ergo_imp_lambda -> ergo_imp_declaration
    | DIFuncTable : string -> ergo_imp_function_table -> ergo_imp_declaration.

    (** Module. *)
    Record ergo_imp_module :=
      mkModuleI
        { modulei_provenance : provenance;
          modulei_namespace : string;
          modulei_declarations : list ergo_imp_declaration; }.

  End Syntax.

  (** Eval-based semantics for ergo_imp *)
  Section Evaluation.
    Context {m : brand_model}.

    Local Open Scope string.

    Definition ergo_imp_lambda_eval
               (f:ergo_imp_lambda)
               (params:list (string * qcert_data)) : eresult qcert_data
      :=
        let jparams :=
            EJson.ejobject (List.map (fun xy => (fst xy, DataToEJson.data_to_ejson (snd xy))) params)
        in
        eresult_of_option
          (lift DataToEJson.ejson_to_data
                (ImpEJsonEval.imp_ejson_function_eval brand_relation_brands f jparams))
          (ERuntimeError dummy_provenance "ErgoImp eval failed") nil.

    Definition ergo_imp_function_table_eval
               (tname:string)
               (fname:string)
               (tf:ergo_imp_function_table)
               (params:list (string * qcert_data)) : eresult qcert_data
      :=
        match tf with
        | Imp.ImpLib tfl =>
          match lookup string_dec tfl fname with
          | None => efailure (ERuntimeError dummy_provenance ("ErgoImp eval cannot find function with name " ++ fname ++ " in table " ++ tname))
          | Some f =>
            ergo_imp_lambda_eval f params
          end
        end.

    Fixpoint ergo_imp_declaration_lookup_function
             (fname:string)
             (m:list ergo_imp_declaration) : option ergo_imp_lambda
      :=
      match m with
      | nil => None
      | DIFunc fname' f :: m' =>
        if string_dec fname' fname
        then Some f
        else ergo_imp_declaration_lookup_function fname m'
      | DIFuncTable _ _ :: m' =>
        ergo_imp_declaration_lookup_function fname m'
      end.

    Fixpoint ergo_imp_declaration_lookup_table
             (tname:string)
             (m:list ergo_imp_declaration) : option ergo_imp_function_table
      :=
      match m with
      | nil => None
      | DIFunc _ _ :: m' =>
        ergo_imp_declaration_lookup_table tname m'
      | DIFuncTable tname' tf :: m' =>
        if string_dec tname' tname
        then Some tf
        else ergo_imp_declaration_lookup_table tname m'
      end.

    Definition ergo_imp_module_eval
               (otname:option string) (fname:string) (m:ergo_imp_module)
               (params: list (string * qcert_data)) : eresult qcert_data
      :=
      match otname with
      | None =>
        match ergo_imp_declaration_lookup_function fname m.(modulei_declarations) with
        | None =>
          efailure (ERuntimeError m.(modulei_provenance) ("ErgoImp eval cannot find function with name " ++ fname))
        | Some f =>
          ergo_imp_lambda_eval f params
        end
      | Some tname =>
        match ergo_imp_declaration_lookup_table fname m.(modulei_declarations) with
        | None =>
          efailure (ERuntimeError m.(modulei_provenance) ("ErgoImp eval cannot find function with name " ++ fname))
        | Some fl =>
          ergo_imp_function_table_eval tname fname fl params
        end
      end.

  End Evaluation.
End ErgoImp.

