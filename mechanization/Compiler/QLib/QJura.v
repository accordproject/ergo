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

Require String.
Require Import Qcert.Compiler.Model.CompilerRuntime.
Require Import Qcert.Compiler.QLib.QLang.

Require Jura.Compiler.QLib.QJOperators.
Require Jura.Compiler.QLib.QJData.
Require Jura.Utils.JResult.
Require Jura.Common.CTO.CTO.
Require Jura.Jura.Lang.Jura.
Require Jura.Jura.Lang.JuraSugar.
Require Jura.JuraCalculus.Lang.JuraCalculus.
Require Jura.JuraCalculus.Lang.JuraCalculusCall.
Require Jura.Translation.JuratoJuraCalculus.
Require Jura.Translation.JuratoJavaScript.
Require Import Jura.Compiler.Model.JuraModel.

Module QJura(juramodel:JuraCompilerModel).

  Module Data := QJData.QJData(juramodel).
  Module Ops := QJOperators.QJOperators(juramodel).

  (** CTO *)
  Definition cto_class : Set
    := CTO.cto_class.

  Definition cto_string : CTO.cto_type
    := CTO.CTOString.
  Definition cto_double : CTO.cto_type
    := CTO.CTODouble.
  Definition cto_long : CTO.cto_type
    := CTO.CTOLong.
  Definition cto_bool : CTO.cto_type
    := CTO.CTOBool.
  Definition cto_class_ref : CTO.cto_class -> CTO.cto_type
    := CTO.CTOClassRef.
  Definition cto_option : CTO.cto_type -> CTO.cto_type
    := CTO.CTOOption.
  Definition cto_structure : list(String.string * CTO.cto_type) -> CTO.cto_type
    := CTO.CTOStructure.
  Definition cto_array : CTO.cto_type -> CTO.cto_type
    := CTO.CTOArray.

  Definition cto_enum : list String.string -> CTO.cto_declaration_kind
    := CTO.CTOEnum.
  Definition cto_transaction : option String.string -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOTransaction.
  Definition cto_concept : option String.string -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOConcept.

  Definition mk_cto_declaration : CTO.cto_class -> CTO.cto_declaration_kind -> CTO.cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : String.string -> list CTO.cto_declaration -> CTO.cto_package
    := CTO.mkCTOPackage.
  
  (** Jura *)
  Definition jura_package : Set 
    := Jura.jura_package.
  Definition jura_contract : Set
    := Jura.jura_contract.
  Definition jura_declaration : Set
    := Jura.jura_declaration.
  Definition jura_clause : Set
    := Jura.jura_clause.
  Definition jura_expr : Set 
    := Jura.jura_expr.

  Definition jvar : String.string -> jura_expr
    := Jura.JVar.

  Definition jcasevalue : Data.data -> Jura.match_case_kind := Jura.CaseValue.
  Definition jcasetype : String.string -> Jura.match_case_kind := Jura.CaseType.

  Definition jconst : Data.data -> jura_expr := Jura.JConst.
  Definition jarray : list jura_expr -> jura_expr := Jura.JArray.
  Definition junaryop : Ops.Unary.op -> jura_expr -> jura_expr
    := Jura.JUnaryOp.
  Definition jbinaryop : Ops.Binary.op -> jura_expr -> jura_expr -> jura_expr 
    := Jura.JBinaryOp.
  Definition jif : jura_expr -> jura_expr -> jura_expr -> jura_expr 
    := Jura.JIf.
  Definition jensure (e1 e2 e3:jura_expr) 
    := Jura.JEnsure e1 (Some e2) e3.
  Definition jensure_default_fail (e1 e3:jura_expr) 
    := Jura.JEnsure e1 None e3.
  Definition jlet (v:String.string) (e1 e2:jura_expr) : jura_expr
    := Jura.JLet v None e1 e2.
  Definition jlet_typed (v:String.string) (t:CTO.cto_type) (e1 e2:jura_expr) : jura_expr
    := Jura.JLet v (Some t) e1 e2.
  Definition jfor : String.string -> jura_expr -> option jura_expr -> jura_expr -> jura_expr
    := Jura.JFor.
  Definition jfuncall : String.string -> list jura_expr -> jura_expr
    := Jura.JFunCall.
  Definition jmatch : jura_expr -> list (Jura.match_case * jura_expr) -> jura_expr -> jura_expr
    := Jura.JMatch.
  Definition jstructure : list (String.string * jura_expr) -> jura_expr 
    := Jura.JStructure.

  Definition jdot : String.string -> jura_expr -> jura_expr 
    := JuraSugar.JDot.
  Definition jreturn : jura_expr -> jura_expr
    := JuraSugar.JReturn.
  Definition jnew : option String.string -> String.string -> list (String.string * jura_expr) -> jura_expr 
    := JuraSugar.JNewSugar.
  Definition jthrow : option String.string -> String.string -> list (String.string * jura_expr) -> jura_expr 
    := JuraSugar.JThrowSugar.
  Definition jthis : jura_expr
    := JuraSugar.JThis.

  (** Jura Calculus *)
  Definition jurac_package : Set 
    := JuraCalculus.jurac_package.
  Definition jurac_contract : Set
    := JuraCalculus.jurac_contract.
  Definition jurac_declaration : Set
    := JuraCalculus.jurac_declaration.
  Definition jurac_clause : Set
    := JuraCalculus.jurac_clause.
  Definition jurac_expr : Set 
    := JuraCalculus.jurac_expr.

  (** Compilation *)
  Definition clause_calculus_from_jura_package :
    String.string -> String.string -> jura_package -> JResult.jresult NNRC.nnrc
    := JuratoJavaScript.clause_calculus_from_package.

  Definition clause_code_from_jura_package :
    String.string -> String.string -> jura_package -> JResult.jresult JavaScript.javascript
    := JuratoJavaScript.clause_code_from_package.

  Definition jura_calculus_package_from_jura_package :
    jura_package -> JResult.jresult jurac_package
    := JuratoJuraCalculus.package_to_calculus.

  Definition clause_code_from_jurac_package :
    String.string -> String.string -> jurac_package -> JResult.jresult JavaScript.javascript
    := JuraCalculustoJavaScript.javascript_of_clause_code_in_package.

  Definition javascript_from_jurac_package :
    jurac_package -> JavaScript.javascript
    := JuraCalculustoJavaScript.javascript_of_package_top.

  Definition javascript_from_jura_package :
    jura_package -> JResult.jresult JavaScript.javascript
    := JuratoJavaScript.javascript_from_package.

  Definition javascript_from_jura_package_with_dispatch :
    option String.string -> jura_package -> JResult.jresult JavaScript.javascript
    := JuratoJavaScript.javascript_from_package_with_dispatch.

End QJura.

