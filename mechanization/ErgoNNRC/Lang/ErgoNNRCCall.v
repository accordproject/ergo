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

Require Import String.
Require Import List.

Require Import Qcert.Utils.ListAdd. (* For zip *)
Require Import Qcert.Utils.Lift.
Require Qcert.Utils.Closure.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.

Section Lambda.
  Definition nnrc_expr_lambda := lambdan.

  Definition lookup_table := string -> option nnrc_expr_lambda.

  Definition add_function_to_table
             (t:lookup_table) (newfname:string) (newcl:lambdan) : lookup_table :=
    fun fname =>
      if (string_dec fname newfname)
      then Some newcl
      else t fname.
  
End Lambda.

Section Patch.
  Definition nnrc_lambda_type_of_lambda_type (t:option unit) : cto_type :=
    CTOAny.
  
  Definition nnrc_lambda_params_of_lambda_params
             (params:list (string * option unit)) : list (string * cto_type) :=
    List.map (fun xy => (fst xy, nnrc_lambda_type_of_lambda_type (snd xy))) params.
    
  Definition nnrc_expr_lambda_of_backend_closure
             (cl:ErgoEnhancedBackend.ergo_backend_closure) : nnrc_expr_lambda :=
    mkLambdaN
      (nnrc_lambda_params_of_lambda_params cl.(Closure.closure_params))
      (nnrc_lambda_type_of_lambda_type cl.(Closure.closure_output))
      cl.(Closure.closure_body).

  Definition lookup_table_of_backend_lookup_table (tbl:ErgoEnhancedBackend.ergo_backend_lookup_table) :=
    fun name => lift nnrc_expr_lambda_of_backend_closure (tbl name).

  Definition nnrc_stdlib : lookup_table :=
    lookup_table_of_backend_lookup_table ErgoEnhancedBackend.ergo_backend_stdlib.

End Patch.

Section ErgoNNRCCall.
  (** Error for function call not found *)
  Definition function_not_found_error (fname:string) : string :=
    "Function '" ++ fname ++ "' not found".

  (** Error for clause call not found *)
  Definition clause_not_found_error (fname:string) : string :=
    "Clause '" ++ fname ++ "' not found".

  (** Error for parameters mismatch in calls *)
  Definition call_params_error (fname:string) : string :=
    "Parameter mistmatch when calling function '" ++ fname ++ "'".

  (** assign each parameter to its effective value.
      only succeeds if the number of parameters is correct.
      Note: we do not support partial function application. *)
  Definition zip_params (params:list string) (el:list nnrc_expr) : option (list (string * nnrc_expr)) :=
    zip params el.
    
  Definition create_call (params:list (string * nnrc_expr)) (body:nnrc_expr) : nnrc_expr :=
    let all_free_vars := map fst params in
    let unshadowed_body := ErgoCodeGen.nnrc_expr_unshadow "_" (fun s => s) all_free_vars body in
    let unconsted_body := ErgoCodeGen.nnrc_expr_subst_const_to_var all_free_vars unshadowed_body in
    let one_param (e:nnrc_expr) (param:string * nnrc_expr) : nnrc_expr :=
        let (pv,pe) := param in
        (ErgoCodeGen.nnrc_expr_let pv pe e)
    in
    fold_left one_param params unconsted_body.

  (** Looks up a function with its parameters. If the function exists and the number of parameters
      is correct, it returns a closed expression computing the call. *)
  Definition lookup_call (t:lookup_table) (fname:string) (el:list nnrc_expr) : eresult nnrc_expr :=
    match t fname with
    | None => efailure (CompilationError (function_not_found_error fname))
    | Some cl =>
      match zip_params (List.map fst cl.(lambdan_params)) el with
      | None => efailure (CompilationError (call_params_error fname))
      | Some params => 
        esuccess (create_call params cl.(lambdan_body))
      end
    end.

End ErgoNNRCCall.

