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
Require Import Qcert.Common.CommonRuntime.
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Jura.Utils.JResult.
Require Import Jura.Jura.Lang.JuraBase.
Require Import Jura.JuraCalculus.Lang.JuraCalculus.

Section JuraCalculusCall.
  Context {fruntime:foreign_runtime}.
  
  Definition jurac_expr_closure := @closure jurac_expr.

  Definition lookup_table := string -> option jurac_expr_closure.

  Definition compose_table (t1 t2:lookup_table) : lookup_table :=
    fun fname =>
      match t1 fname with
      | None => t2 fname
      | Some cl => Some cl
      end.

  Definition add_function_to_table
             (t:lookup_table) (newfname:string) (newcl:@closure jurac_expr) : lookup_table :=
    fun fname =>
      if (string_dec fname newfname)
      then Some newcl
      else t fname.
  
  (** Error for function calls *)
  Definition call_error (fname:string) : string :=
    "Function '" ++ fname ++ "' not found".

  Definition call_params_error (fname:string) : string :=
    "Parameter mistmatch when calling function '" ++ fname ++ "'".

  (** assign each parameter to its effective value.
      only succeeds if the number of parameters is correct.
      Note: we do not support partial function application. *)
  Definition zip_params (params:list string) (el:list jurac_expr) : option (list (string * jurac_expr)) :=
    zip params el.
    
  Definition create_call (params:list (string * jurac_expr)) (body:jurac_expr) : jurac_expr :=
    let all_free_vars := map fst params in
    let unshadowed_body := unshadow "_" (fun s => s) all_free_vars body in
    let unconsted_body := nnrc_subst_const_to_var all_free_vars unshadowed_body in
    let one_param (e:jurac_expr) (param:string * jurac_expr) : jurac_expr :=
        let (pv,pe) := param in
        (NNRCLet pv pe e)
    in
    fold_left one_param params unconsted_body.

  (** Looks up a function with its parameters. If the function exists and the number of parameters
      is correct, it returns a closed expression computing the call. *)
  Definition lookup_call (t:lookup_table) (fname:string) (el:list jurac_expr) : jresult jurac_expr :=
    match t fname with
    | None => jfailure (CompilationError (call_error fname))
    | Some cl =>
      match zip_params (List.map fst cl.(closure_params)) el with
      | None => jfailure (CompilationError (call_params_error fname))
      | Some params => 
        jsuccess (create_call params cl.(closure_body))
      end
    end.
    
  (** Looks up a clause with its parameters. If the function exists and the number of parameters
      is correct, it returns a closed expression computing the call. *)
  Definition lookup_clause_call
             (t:lookup_table)
             (cref:class_ref)
             (fname:string)
             (el:list jurac_expr) : jresult jurac_expr :=
    match t fname with
    | None => jfailure (CompilationError (call_error fname))
    | Some cl =>
      match zip_params (List.map fst cl.(closure_params)) el with
      | None => jfailure (CompilationError (call_params_error fname))
      | Some params => 
        jsuccess (create_call params cl.(closure_body))
      end
    end.

End JuraCalculusCall.

