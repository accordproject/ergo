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
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.

Section Lambda.
  Definition ergoc_expr_lambda := @lambda ergoc_expr.

  Definition lookup_table := string -> option ergoc_expr_lambda.

  Definition add_function_to_table
             (t:lookup_table) (newfname:string) (newcl:@lambda ergoc_expr) : lookup_table :=
    fun fname =>
      if (string_dec fname newfname)
      then Some newcl
      else t fname.
  
End Lambda.

Section Patch.
  Definition ergoc_lambda_type_of_lambda_type (t:option unit) : option cto_type :=
    None.
  
  Definition ergoc_lambda_params_of_lambda_params
             (params:list (string * option unit)) : list (string * option cto_type) :=
    List.map (fun xy => (fst xy, ergoc_lambda_type_of_lambda_type (snd xy))) params.
    
  Definition ergoc_expr_lambda_of_backend_closure
             (cl:ErgoEnhancedBackend.ergo_backend_closure) : ergoc_expr_lambda :=
    mkLambda
      (ergoc_lambda_params_of_lambda_params cl.(Closure.closure_params))
      (ergoc_lambda_type_of_lambda_type cl.(Closure.closure_output))
      None
      cl.(Closure.closure_body).

  Definition lookup_table_of_backend_lookup_table (tbl:ErgoEnhancedBackend.ergo_backend_lookup_table) :=
    fun name => lift ergoc_expr_lambda_of_backend_closure (tbl name).

  Definition ergoc_stdlib : lookup_table :=
    lookup_table_of_backend_lookup_table ErgoEnhancedBackend.ergo_backend_stdlib.

End Patch.

Section ErgoCalculusCall.
  (** Error for function calls *)
  Definition call_error (fname:string) : string :=
    "Function '" ++ fname ++ "' not found".

  Definition call_params_error (fname:string) : string :=
    "Parameter mistmatch when calling function '" ++ fname ++ "'".

  (** assign each parameter to its effective value.
      only succeeds if the number of parameters is correct.
      Note: we do not support partial function application. *)
  Definition zip_params (params:list string) (el:list ergoc_expr) : option (list (string * ergoc_expr)) :=
    zip params el.
    
  Definition create_call (params:list (string * ergoc_expr)) (body:ergoc_expr) : ergoc_expr :=
    let all_free_vars := map fst params in
    let unshadowed_body := ErgoCodeGen.ergoc_expr_unshadow "_" (fun s => s) all_free_vars body in
    let unconsted_body := ErgoCodeGen.ergoc_expr_subst_const_to_var all_free_vars unshadowed_body in
    let one_param (e:ergoc_expr) (param:string * ergoc_expr) : ergoc_expr :=
        let (pv,pe) := param in
        (ErgoCodeGen.ergoc_expr_let pv pe e)
    in
    fold_left one_param params unconsted_body.

  (** Looks up a function with its parameters. If the function exists and the number of parameters
      is correct, it returns a closed expression computing the call. *)
  Definition lookup_call (t:lookup_table) (fname:string) (el:list ergoc_expr) : eresult ergoc_expr :=
    match t fname with
    | None => efailure (CompilationError (call_error fname))
    | Some cl =>
      match zip_params (List.map fst cl.(lambda_params)) el with
      | None => efailure (CompilationError (call_params_error fname))
      | Some params => 
        esuccess (create_call params cl.(lambda_body))
      end
    end.
    
  (** Looks up a clause with its parameters. If the function exists and the number of parameters
      is correct, it returns a closed expression computing the call. *)
  Definition lookup_clause_call
             (t:lookup_table)
             (cref:class_ref)
             (fname:string)
             (el:list ergoc_expr) : eresult ergoc_expr :=
    match t fname with
    | None => efailure (CompilationError (call_error fname))
    | Some cl =>
      match zip_params (List.map fst cl.(lambda_params)) el with
      | None => efailure (CompilationError (call_params_error fname))
      | Some params => 
        esuccess (create_call params cl.(lambda_body))
      end
    end.

End ErgoCalculusCall.

