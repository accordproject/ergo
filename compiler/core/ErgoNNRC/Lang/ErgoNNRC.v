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

(** ErgoNNRC is an IL with function tables where the body of those functions is written as NNRC expressions. It is the main interface with Q*cert for code-generation. *)

(** * Abstract Syntax *)

Require Import String.
Require Import List.
Require Import Qcert.Driver.CompEval.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Backend.QLib.

Section ErgoNNRC.
  Section Syntax.
    Context {m : brand_model}.

    (** Expression *)
    Definition ergo_nnrc_expr := QcertCodeGen.nnrc_expr.
    Definition ergo_nnrc_type := qcert_type.

    (** Function *)
    Record ergo_nnrc_lambda :=
      mkLambdaN
        { lambdan_provenance : provenance;
          lambdan_params: list (string * ergo_nnrc_type);
          lambdan_output : ergo_nnrc_type;
          lambdan_body : ergo_nnrc_expr; }.

    (** Function table *)
    Record ergo_nnrc_function_table :=
      mkFuncTableN
        { function_tablen_provenance : provenance;
          function_tablen_funs : list (string * ergo_nnrc_lambda); }.

    (** Declaration *)
    Inductive ergo_nnrc_declaration :=
    | DNFunc : string -> ergo_nnrc_lambda -> ergo_nnrc_declaration
    | DNFuncTable : string -> ergo_nnrc_function_table -> ergo_nnrc_declaration.

    (** Module. *)
    Record ergo_nnrc_module :=
      mkModuleN
        { modulen_provenance : provenance;
          modulen_namespace : string;
          modulen_declarations : list ergo_nnrc_declaration; }.

  End Syntax.

  Record result_file :=
    mkResultFile
      { res_contract_name : option string;
        res_file : string;
        res_content : nstring; }.

  (** Eval-based semantics for ergo_nnrc *)
  Section Evaluation.
    Context {m : brand_model}.

    Local Open Scope string.

    Definition ergo_nnrc_lambda_eval
               (f:ergo_nnrc_lambda)
               (params:list (string * qcert_data)) : eresult qcert_data
      :=
        let e := f.(lambdan_body) in
        let prov := f.(lambdan_provenance) in
        eresult_of_option (eval_nnrc e params) (ERuntimeError prov "ErgoNNRC eval failed") nil.

    Definition ergo_nnrc_function_table_eval
               (tname:string)
               (fname:string)
               (tf:ergo_nnrc_function_table)
               (params:list (string * qcert_data)) : eresult qcert_data
      :=
        match lookup string_dec tf.(function_tablen_funs) fname with
        | None => efailure (ERuntimeError tf.(function_tablen_provenance) ("ErgoNNRC eval cannot find function with name " ++ fname ++ " in table " ++ tname))
        | Some f =>
          ergo_nnrc_lambda_eval f params
        end.

    Fixpoint ergo_nnrc_declaration_lookup_function
             (fname:string)
             (m:list ergo_nnrc_declaration) : option ergo_nnrc_lambda
      :=
      match m with
      | nil => None
      | DNFunc fname' f :: m' =>
        if string_dec fname' fname
        then Some f
        else ergo_nnrc_declaration_lookup_function fname m'
      | DNFuncTable _ _ :: m' =>
        ergo_nnrc_declaration_lookup_function fname m'
      end.

    Fixpoint ergo_nnrc_declaration_lookup_table
             (tname:string)
             (m:list ergo_nnrc_declaration) : option ergo_nnrc_function_table
      :=
      match m with
      | nil => None
      | DNFunc _ _ :: m' =>
        ergo_nnrc_declaration_lookup_table tname m'
      | DNFuncTable tname' tf :: m' =>
        if string_dec tname' tname
        then Some tf
        else ergo_nnrc_declaration_lookup_table tname m'
      end.

    (** Main semantics for ErgoNNRC, based on contract invokation.
        [ergo_nnrc_invoke m callname params] invokes [callname] in module [m] with parameters [params]
        [callname] can either be:
         - [(None,fname)] invoking function [fname], or
         - [(Some cname, fname)] invoking clause [fname] in contract [cname] *)
    Definition ergo_nnrc_invoke
               (m:ergo_nnrc_module)
               (callname: option string * string)
               (params: list (string * qcert_data)) : eresult qcert_data
      :=
        match callname with
        (** Calls a function *)
        | (None,fname) =>
          match ergo_nnrc_declaration_lookup_function fname m.(modulen_declarations) with
          | None =>
            efailure (ERuntimeError m.(modulen_provenance) ("ErgoNNRC eval cannot find function with name " ++ fname))
          | Some f =>
            ergo_nnrc_lambda_eval f params
          end
        (** Calls a clause in a contract *)
        | (Some cname, fname) =>
          match ergo_nnrc_declaration_lookup_table fname m.(modulen_declarations) with
          | None =>
            efailure (ERuntimeError m.(modulen_provenance) ("ErgoNNRC eval cannot find function with name " ++ fname))
          | Some fl =>
            ergo_nnrc_function_table_eval cname fname fl params
          end
        end.

  End Evaluation.
End ErgoNNRC.

