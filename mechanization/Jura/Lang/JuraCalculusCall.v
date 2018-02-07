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
Require Import Error.
Require Import JuraCalculus.

Section JuraCalculusCall.
  (** Generic function closure over expressions in [A].
      All free variables in A have to be declared in the list of parameters. *)
  Record closure {A} :=
    mkClosure
      { closure_params: list string;
        closure_body : A; }.

  Context {fruntime:foreign_runtime}.
  
  Definition jurac_expr_closure := @closure jurac_expr.

  Definition lookup_table := string -> option jurac_expr_closure.

  Definition compose_table (t1 t2:lookup_table) : lookup_table :=
    fun fname =>
      match t1 fname with
      | None => t2 fname
      | Some cl => Some cl
      end.

  (** Error for function calls *)
  Definition call_error (fname:string) : string :=
    "Function '" ++ fname ++ "' not found".

  Definition call_params_error (fname:string) : string :=
    "Parameter mistmatch when calling function '" ++ fname ++ "'".

  Definition zip_params (params:list string) (el:list jurac_expr) : option (list (string * jurac_expr)) :=
    zip params el.
    
  (* params are the effective parameters for the call,
     i.e., a list of parameters with the expression that computes their values.
     body is the body of the function.
     after the call has been constructed, the function should have no free variables. *)
  Definition create_call (params:list (string * jurac_expr)) (body:jurac_expr) : jurac_expr :=
    let one_param (e:jurac_expr) (param:string * jurac_expr) : jurac_expr :=
        let (pv,pe) := param in
        (NNRCLet pv pe e)
    in fold_left one_param params body.
    
  Definition lookup_call (t:lookup_table) (fname:string) (el:list jurac_expr) : jresult jurac_expr :=
    match t fname with
    | None => jfailure (CompilationError (call_error fname))
    | Some cl =>
      match zip_params cl.(closure_params) el with
      | None => jfailure (CompilationError (call_params_error fname))
      | Some params => 
        jsuccess (create_call params cl.(closure_body))
      end
    end.
    
End JuraCalculusCall.

