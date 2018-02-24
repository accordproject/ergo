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
Require Import JuraBase.
Require Import Jura.
Require Import Jura.Compiler.Model.JuraRuntime.
Require Import Jura.Compiler.JuraCompiler.

Section HelloWorld.
  Open Scope string_scope.
  
  (*
package org.accordproject.helloworld

contract HelloWorld over TemplateModel {
   // Simple Clause
   clause helloworld(request Request) Response {
       new Response{ output: "Hello " + this.name + " (" + request.input +")" }
  }
}
*)

  Definition cl1 :=
    mkClause "helloworld"
             (mkClosure
                (("request", Some "Request")::nil)
                (Some "Response")
                None
                (JVar "request")).

  Definition c1 :=
    mkContract "HelloWorld"
               "TemplateModel"
               ((Clause cl1)::nil).
  
  Definition p1 :=
    mkPackage "org.accordproject.helloworld"
              ((JContract c1)::nil).

  (*
  Section translate.
    Eval vm_compute in (JuraCompiler.javascript_from_jura_package_with_dispatch None p1).

    Definition t := JuraRuntime.jura_compiler_foreign_jura.
    
    Require Import JuratoJavaScript.
    Require Import JuratoJuraCalculus.
    Require Import Error.

    Definition p := add_dispatch_fun None p1.
    Definition pc := jolift (@package_to_calculus _ t) p.
    Definition f1 := jolift (lookup_dispatch dispatch_fun_name) pc.
    Eval vm_compute in f1.
    Print jresult.
    Require Import NNRCRuntime.
    Definition ft :=
      match f1 with | Success _ _ f => f | Failure _ _ _ => ("","",mkFunc "" (mkClosure nil None None (NNRCVar ""))) end.
    Definition f := (snd ft).
    Eval vm_compute in f.
    
    Definition coname : option string := None.
    Require Import JuraCalculustoJavaScript.
    Definition fname := function_name_of_contract_clause_name coname f.(func_name).
    Definition quotel := """".
    Definition eol := "\n".
    Definition res := javascript_function_of_body f.(func_closure).(closure_body) fname eol quotel ++ eol.
    Eval vm_compute in res.
    Require Import NNRCtoJavaScript.
    Definition input_v := "context".
    Definition init_indent := 0.
    Definition e := f.(func_closure).(closure_body).
    Definition res1 := nnrcToJSFun input_v e init_indent eol quotel (input_v::nil) fname.
    Eval vm_compute in res1.
    Definition ivs := (input_v::nil).
    Definition e' := closeFreeVars jsSafeSeparator jsIdentifierSanitize (NNRCVar input_v) e ivs.
    Eval vm_compute in e'.
    Require Import Utils.
    Definition all_free_vars := bdistinct (nnrc_global_vars e).
    Eval vm_compute in all_free_vars.
    Definition params := ivs.
    Definition avoid := map (fun x => "c$" ++ x) all_free_vars.
    Eval vm_compute in avoid.
    Definition unshadowed_e := unshadow jsSafeSeparator jsIdentifierSanitize avoid e.
    Eval vm_compute in unshadowed_e.
    Definition unconsted_e := nnrc_subst_const_to_var all_free_vars unshadowed_e.
    Eval vm_compute in unconsted_e.
    Definition input_e := NNRCVar "context".
    Definition wrap_one_free_var (e':nnrc) (fv:string) : nnrc :=
          if (in_dec string_dec fv all_free_vars)
          then e'
          else
            (* note that this is a bit hacky, and relies on the NNRCLet translation to turn this into "vc$", 
               matching up with the translation of NNRCGetConstant *)
            (NNRCLet ("c$" ++ fv) (NNRCUnop (OpDot fv) input_e) e').
    Eval vm_compute in (fold_left wrap_one_free_var all_free_vars unconsted_e).
    Definition i := init_indent.
    Eval vm_compute in (nnrcToJSFunStubConstantsAsFunction e' i eol quotel ivs fname). *)
    
End HelloWorld.

