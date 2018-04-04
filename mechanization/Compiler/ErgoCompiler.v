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

Require Ergo.Version.
Require Ergo.Common.Utils.JNames.
Require Ergo.Common.Utils.JResult.
Require Ergo.Common.CTO.CTO.
Require Ergo.Ergo.Lang.Ergo.
Require Ergo.Ergo.Lang.ErgoSugar.
Require Ergo.ErgoCalculus.Lang.ErgoCalculus.
Require Ergo.ErgoCalculus.Lang.ErgoCalculusCall.
Require Ergo.Translation.ErgotoErgoCalculus.
Require Ergo.Translation.ErgotoJavaScript.
Require Ergo.Backend.ErgoBackend.

Module ErgoCompiler.

  Definition ergo_version := Version.ergo_version.
  
  Module Data := ErgoBackend.ErgoData.
  Module Ops := ErgoBackend.ErgoOps.

  (** CTO *)
  Definition cto_class : Set
    := JNames.class_ref.
  Definition mk_class_ref : option String.string -> String.string -> cto_class
    := JNames.mkClassRef.

  Definition cto_boolean : CTO.cto_type
    := CTO.CTOBoolean.
  Definition cto_string : CTO.cto_type
    := CTO.CTOString.
  Definition cto_double : CTO.cto_type
    := CTO.CTODouble.
  Definition cto_long : CTO.cto_type
    := CTO.CTOLong.
  Definition cto_integer : CTO.cto_type
    := CTO.CTOInteger.
  Definition cto_dateTime : CTO.cto_type
    := CTO.CTODateTime.
  Definition cto_class_ref : cto_class -> CTO.cto_type
    := CTO.CTOClassRef.
  Definition cto_option : CTO.cto_type -> CTO.cto_type
    := CTO.CTOOption.
  Definition cto_record : list(String.string * CTO.cto_type) -> CTO.cto_type
    := CTO.CTORecord.
  Definition cto_array : CTO.cto_type -> CTO.cto_type
    := CTO.CTOArray.

  Definition cto_enum : list String.string -> CTO.cto_declaration_kind
    := CTO.CTOEnum.
  Definition cto_transaction : option String.string -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOTransaction.
  Definition cto_concept : option String.string -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOConcept.

  Definition mk_cto_declaration : cto_class -> CTO.cto_declaration_kind -> CTO.cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : String.string -> list CTO.cto_declaration -> CTO.cto_package
    := CTO.mkCTOPackage.
  
  (** Ergo *)
  Definition ergo_package : Set 
    := Ergo.ergo_package.
  Definition ergo_contract : Set
    := Ergo.ergo_contract.
  Definition ergo_declaration : Set
    := Ergo.ergo_declaration.
  Definition ergo_clause : Set
    := Ergo.ergo_clause.
  Definition ergo_expr : Set 
    := Ergo.ergo_expr.

  Definition jvar : String.string -> ergo_expr
    := Ergo.JVar.

  Definition jcasevalue : Data.data -> Ergo.match_case_kind := Ergo.CaseValue.
  Definition jcasetype : String.string -> Ergo.match_case_kind := Ergo.CaseType.

  Definition jconst : Data.data -> ergo_expr := Ergo.JConst.
  Definition jarray : list ergo_expr -> ergo_expr := Ergo.JArray.
  Definition junaryop : Ops.Unary.op -> ergo_expr -> ergo_expr
    := Ergo.JUnaryOp.
  Definition jbinaryop : Ops.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr 
    := Ergo.JBinaryOp.
  Definition jif : ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr 
    := Ergo.JIf.
  Definition jenforce (e1 e2 e3:ergo_expr) 
    := Ergo.JEnforce e1 (Some e2) e3.
  Definition jenforce_default_fail (e1 e3:ergo_expr) 
    := Ergo.JEnforce e1 None e3.
  Definition jlet (v:String.string) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.JLet v None e1 e2.
  Definition jlet_typed (v:String.string) (t:CTO.cto_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.JLet v (Some t) e1 e2.
  Definition jfor : String.string -> ergo_expr -> option ergo_expr -> ergo_expr -> ergo_expr
    := Ergo.JFor.
  Definition jfuncall : String.string -> list ergo_expr -> ergo_expr
    := Ergo.JFunCall.
  Definition jmatch : ergo_expr -> list (Ergo.match_case * ergo_expr) -> ergo_expr -> ergo_expr
    := Ergo.JMatch.
  Definition jrecord : list (String.string * ergo_expr) -> ergo_expr 
    := Ergo.JRecord.

  Definition jdot : String.string -> ergo_expr -> ergo_expr 
    := ErgoSugar.JDot.
  Definition jreturn : ergo_expr -> ergo_expr
    := ErgoSugar.JReturn.
  Definition jreturnsetstate : ergo_expr -> ergo_expr -> ergo_expr
    := ErgoSugar.JReturnSetState.
  Definition jnew : option String.string -> String.string -> list (String.string * ergo_expr) -> ergo_expr 
    := ErgoSugar.JNewSugar.
  Definition jthrow : option String.string -> String.string -> list (String.string * ergo_expr) -> ergo_expr 
    := ErgoSugar.JThrowSugar.
  Definition jthis_contract : ergo_expr
    := Ergo.JThisContract.
  Definition jthis_clause : ergo_expr
    := Ergo.JThisClause.
  Definition jthis_state : ergo_expr
    := Ergo.JThisState.

  (** Ergo Calculus *)
  Definition ergoc_package : Set 
    := ErgoCalculus.ergoc_package.
  Definition ergoc_contract : Set
    := ErgoCalculus.ergoc_contract.
  Definition ergoc_declaration : Set
    := ErgoCalculus.ergoc_declaration.
  Definition ergoc_clause : Set
    := ErgoCalculus.ergoc_clause.
  Definition ergoc_expr : Set 
    := ErgoCalculus.ergoc_expr.

  (** Compilation *)
  Definition clause_calculus_from_ergo_package :
    String.string -> String.string -> ergo_package -> JResult.jresult NNRC.nnrc
    := ErgotoJavaScript.clause_calculus_from_package.

  Definition clause_code_from_ergo_package :
    String.string -> String.string -> ergo_package -> JResult.jresult JavaScript.javascript
    := ErgotoJavaScript.clause_code_from_package.

  Definition ergo_calculus_package_from_ergo_package :
    ergo_package -> JResult.jresult ergoc_package
    := ErgotoErgoCalculus.package_to_calculus.

  Definition clause_code_from_ergoc_package :
    String.string -> String.string -> ergoc_package -> JResult.jresult JavaScript.javascript
    := ErgoCalculustoJavaScript.javascript_of_clause_code_in_package.

  Definition javascript_from_ergoc_package :
    ergoc_package -> JavaScript.javascript
    := ErgoCalculustoJavaScript.javascript_of_package_top.

  Definition javascript_from_ergo_package :
    ergo_package -> JResult.jresult JavaScript.javascript
    := ErgotoJavaScript.javascript_from_package.

  Definition javascript_from_ergo_package_with_dispatch :
    option String.string -> ergo_package -> JResult.jresult JavaScript.javascript
    := ErgotoJavaScript.javascript_from_package_with_dispatch.

End ErgoCompiler.

