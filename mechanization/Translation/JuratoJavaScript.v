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

Require Import Jura.Backend.ForeignJura.
Require Import Jura.Backend.JuraBackend.
Require Import Jura.Common.Utils.JResult.
Require Import Jura.Common.CTO.CTO.
Require Import Jura.Jura.Lang.JuraBase.
Require Import Jura.Jura.Lang.Jura.
Require Import Jura.JuraCalculus.Lang.JuraCalculusCall.
Require Import Jura.Translation.JuratoJuraCalculus.
Require Import Jura.Translation.JuraCalculustoJavaScript.

Section JuratoJavaScript.
  Definition clause_calculus_from_package
             (coname:string) (clname:string) (p:jura_package) : jresult nnrc :=
    let pc := package_to_calculus p in
    jolift (lookup_clause_code_from_package coname clname) pc.

  (* Context *)
  Definition clause_code_from_package
             (coname:string) (clname:string) (p:jura_package) : jresult javascript :=
    let pc := package_to_calculus p in
    jolift (javascript_of_clause_code_in_package coname clname) pc.

  Definition dispatch_params_error (cname:string) : string :=
    "Parameter mistmatch when dispatching to '" ++ cname ++ "'".

  Definition create_call
             (cname:string)
             (v0:string)
             (effparam0:jura_expr)
             (effparamrest:list jura_expr)
             (callparams:list (string * option cto_type)) :=
    let zipped := zip callparams (effparam0 :: effparamrest) in
    match zipped with
    | None => jfailure (CompilationError "Parameter mismatch during dispatch")
    | Some _ =>
      jsuccess (JFunCall cname (JVar v0 :: effparamrest))
    end.

  Definition case_of_sig
             (namespace:option string)
             (v0:string)
             (effparam0:jura_expr)
             (effparamrest:list jura_expr)
             (s:signature) : jresult (match_case * jura_expr) :=
    let (cname, callparams) := s in
    match callparams with
    | nil => jfailure (CompilationError ("Cannot dispatch if not at least one parameter "++cname))
    | (param0,None)::otherparams =>
      jfailure (CompilationError ("No parameter can be used for dispatch in "++cname))
    | (param0, Some (CTOClassRef type0))::otherparams =>
      jlift (fun x =>
               let type0 := brand_of_class_ref namespace (mkClassRef None type0) in
               ((Some v0,CaseType type0),x))
            (create_call cname v0 effparam0 effparamrest callparams)
    | (param0, Some _)::otherparams =>
      jfailure (CompilationError ("Cannot dispatch on non-class type "++cname))
    end.

  Definition match_of_sigs
             (namespace:option string)
             (v0:string)
             (effparam0:jura_expr)
             (effparamrest:list jura_expr)
             (ss:list signature) :=
    jlift (fun s =>
             JMatch effparam0
                     s
                     (JThrow (mkClassRef None "Error"%string)
                             (("message"%string,JConst (JuraData.dstring ""))::nil)))
          (jmaplift (case_of_sig namespace v0 effparam0 effparamrest) ss).

  Definition dispatch_fun_name :=
    "dispatch"%string.
  
  Definition match_of_sigs_top
             (namespace:option string)
             (effparams:list jura_expr)
             (ss:list signature) :=
    match effparams with
    | nil => jfailure (CompilationError ("Cannot dispatch if not at least one effective parameter"))
    | effparam0 :: effparamrest =>
      let v0 := ("$"++dispatch_fun_name)%string in (** XXX To be worked on *)
      match_of_sigs namespace v0 effparam0 effparamrest ss
    end.

  Definition add_dispatch_fun (oconame:option string) (p:jura_package) : jresult jura_package :=
    let sigs := lookup_package_signatures_for_contract oconame p in
    let effparams := JVar "request"%string :: nil in
    let dispatch_fun_decl :=
        jlift
          (fun disp =>
             (JFunc
                (mkFunc dispatch_fun_name
                        (mkClosure
                           (("request"%string,None)::nil)
                           None
                           None
                           disp))))
          (match_of_sigs_top p.(package_namespace) effparams sigs)
    in
    jlift (fun disp =>
             mkPackage
               p.(package_namespace)
                   (p.(package_statements) ++ (disp::nil)))
          dispatch_fun_decl.

  Definition javascript_from_package
             (p:jura_package) : jresult javascript :=
    let pc := package_to_calculus p in
    jlift javascript_of_package_top pc.

  Definition cast_dispatch_to_classes request response :=
    match request, response with
    | CTOClassRef req, CTOClassRef resp =>
      jsuccess (req, resp)
    | _, _ => jfailure (CompilationError ("Cannot dispatch on non-class types"))
    end.
  
  Definition javascript_from_package_with_dispatch
             (oconame:option string)
             (p:jura_package) : jresult javascript :=
    let p := add_dispatch_fun oconame p in
    let pc := jolift package_to_calculus p in
    let f := jolift (lookup_dispatch dispatch_fun_name) pc in
    jolift (fun xyz =>
             let '(request,response,f) := xyz in
             jlift (fun xy =>
                      javascript_of_package_with_dispatch_top (fst xy) (snd xy) f) (cast_dispatch_to_classes request response)) f.

End JuratoJavaScript.

