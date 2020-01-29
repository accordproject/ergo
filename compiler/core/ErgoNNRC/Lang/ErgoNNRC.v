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
Require Import ErgoSpec.Backend.QLib.

Section ErgoNNRC.
  Section Syntax.
    Context {m : brand_model}.

    (** Expression *)
    Definition nnrc_expr := QcertCodeGen.nnrc_expr.
    Definition nnrc_type := qcert_type.

    (** Functions *)
    Record nnrc_lambda :=
      mkLambdaN
        { nnrc_lambda_params: list (string * nnrc_type);
          nnrc_lambda_output : nnrc_type;
          nnrc_lambda_body : nnrc_expr; }.

    (** Function table *)
    Record nnrc_function_table :=
      mkFuncTableN
        { function_tablen_name : string;
          function_tablen_funs : list (string * nnrc_lambda); }.

    (** Declaration *)
    Inductive nnrc_declaration :=
    | DNFunc : string -> nnrc_lambda -> nnrc_declaration
    | DNFuncTable : nnrc_function_table -> nnrc_declaration.

    (** Module. *)
    Record nnrc_module :=
      mkModuleN
        { modulen_namespace : string;
          modulen_declarations : list nnrc_declaration; }.

  End Syntax.

  Record result_file :=
    mkResultFile {
        res_contract_name : option string;
        res_file : string;
        res_content : nstring;
      }.

  Section Evaluation.
    
  End Evaluation.
End ErgoNNRC.

