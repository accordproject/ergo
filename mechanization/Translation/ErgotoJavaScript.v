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

(** Translates contract logic to calculus *)

Require Import String.
Require Import List.
Require Import Qcert.Utils.ListAdd. (* For zip *)
Require Import Qcert.Compiler.Driver.CompLang.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculusCall.
Require Import ErgoSpec.Translation.ErgotoErgoCalculus.
Require Import ErgoSpec.Translation.ErgoCalculustoJavaScript.

Section ErgotoJavaScript.
  Definition clause_calculus_from_package
             (ctos:list cto_package)
             (coname:string) (clname:string) (p:ergo_package) : eresult nnrc :=
    let pc := package_to_calculus ctos p in
    eolift (lookup_clause_code_from_package coname clname) pc.

  (* Context *)
  Definition clause_code_from_package
             (ctos:list cto_package)
             (coname:string) (clname:string) (p:ergo_package) : eresult javascript :=
    let pc := package_to_calculus ctos p in
    eolift (javascript_of_clause_code_in_package coname clname) pc.

  Definition dispatch_params_error (cname:string) : string :=
    "Parameter mistmatch when dispatching to '" ++ cname ++ "'".

  Definition create_call
             (cname:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (callparams:list (string * option cto_type)) :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => efailure (CompilationError "Parameter mismatch during dispatch")
    | Some _ =>
      esuccess (ECall cname (EVar v0 :: effparamrest))
    end.

  Definition case_of_sig
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (s:signature) : eresult (match_case * ergo_expr) :=
    let (cname, callparams) := s in
    match callparams with
    | nil => efailure (CompilationError ("Cannot dispatch if not at least one parameter "++cname))
    | (param0,None)::otherparams =>
      efailure (CompilationError ("No parameter can be used for dispatch in "++cname))
    | (param0, Some (CTOClassRef type0))::otherparams =>
      elift (fun x =>
               let type0 := absolute_ref_of_relative_ref namespace type0 in
               ((Some v0,CaseType type0),x))
            (create_call cname v0 effparam0 effparamrest callparams)
    | (param0, Some _)::otherparams =>
      efailure (CompilationError ("Cannot dispatch on non-class type "++cname))
    end.

  Definition match_of_sigs
             (namespace:string)
             (v0:string)
             (effparam0:ergo_expr)
             (effparamrest:list ergo_expr)
             (ss:list signature) :=
    elift (fun s =>
             EMatch effparam0
                     s
                     (EThrow (mkClassRef None "Error"%string)
                             (("message"%string, EConst (ErgoData.dstring ""))::nil)))
          (emaplift (case_of_sig namespace v0 effparam0 effparamrest) ss).

  Definition dispatch_fun_name :=
    "dispatch"%string.
  
  Definition match_of_sigs_top
             (namespace:string)
             (effparams:list ergo_expr)
             (ss:list signature) :=
    match effparams with
    | nil => efailure (CompilationError ("Cannot dispatch if not at least one effective parameter"))
    | effparam0 :: effparamrest =>
      let v0 := ("$"++dispatch_fun_name)%string in (** XXX To be worked on *)
      match_of_sigs namespace v0 effparam0 effparamrest ss
    end.

  Definition add_dispatch_fun (oconame:option string) (p:ergo_package) : eresult ergo_package :=
    let sigs := lookup_package_signatures_for_contract oconame p in
    let effparams := EVar "request"%string :: nil in
    let dispatch_fun_decl :=
        elift
          (fun disp =>
             (EFunc
                (mkFunc dispatch_fun_name
                        (mkLambda
                           (("request"%string,None)::nil)
                           None
                           None
                           disp))))
          (match_of_sigs_top p.(package_namespace) effparams sigs)
    in
    elift (fun disp =>
             mkPackage
               p.(package_namespace)
                   (p.(package_statements) ++ (disp::nil)))
          dispatch_fun_decl.

  Definition javascript_from_package
             (ctos:list cto_package)
             (p:ergo_package) : eresult javascript :=
    let pc := package_to_calculus ctos p in
    elift javascript_of_package_top pc.

  Definition cast_dispatch_to_classes request response :=
    match request, response with
    | CTOClassRef req, CTOClassRef resp =>
      esuccess (req, resp)
    | _, _ => efailure (CompilationError ("Cannot dispatch on non-class types"))
    end.
  
  Definition javascript_from_package_with_dispatch
             (ctos:list cto_package)
             (oconame:option string)
             (p:ergo_package) : eresult javascript :=
    let p := add_dispatch_fun oconame p in
    let pc := eolift (package_to_calculus ctos) p in
    let f := eolift (lookup_dispatch dispatch_fun_name) pc in
    eolift (fun xyz =>
             let '(request,response,f) := xyz in
             elift (fun xy =>
                      javascript_of_package_with_dispatch_top (fst xy) (snd xy) f) (cast_dispatch_to_classes request response)) f.

End ErgotoJavaScript.

