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

Require ErgoSpec.Version.
Require ErgoSpec.Backend.ErgoBackend.
Require ErgoSpec.Common.Utils.ENames.
Require ErgoSpec.Common.Utils.EResult.
Require ErgoSpec.Common.Utils.EImport.
Require ErgoSpec.Common.CTO.CTO.
Require ErgoSpec.Common.Pattern.EPattern.
Require ErgoSpec.Ergo.Lang.Ergo.
Require ErgoSpec.Ergo.Lang.ErgoSugar.
Require ErgoSpec.Translation.ErgotoJavaScript.
Require ErgoSpec.Translation.ErgotoJava.
Require ErgoSpec.Translation.ErgotoJavaScriptCicero.

Module ErgoCompiler.

  Definition ergo_version := Version.ergo_version.
  
  Module Data := ErgoBackend.ErgoData.
  Module Ops := ErgoBackend.ErgoOps.

  (** CTO *)
  Definition name_ref : Set
    := ENames.name_ref.
  Definition mk_relative_ref : option String.string -> String.string -> name_ref
    := ENames.RelativeRef.
  Definition mk_absolute_ref : String.string -> name_ref
    := ENames.AbsoluteRef.

  Definition cto_any : CTO.cto_type
    := CTO.CTOAny.
  Definition cto_none : CTO.cto_type
    := CTO.CTONone.
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
  Definition cto_class_ref : name_ref -> CTO.cto_type
    := CTO.CTOClassRef.
  Definition cto_option : CTO.cto_type -> CTO.cto_type
    := CTO.CTOOption.
  Definition cto_record : list(String.string * CTO.cto_type) -> CTO.cto_type
    := CTO.CTORecord.
  Definition cto_array : CTO.cto_type -> CTO.cto_type
    := CTO.CTOArray.

  Definition cto_enum : list String.string -> CTO.cto_declaration_kind
    := CTO.CTOEnum.
  Definition cto_transaction : option name_ref -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOTransaction.
  Definition cto_concept : option name_ref -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_kind
    := CTO.CTOConcept.

  Definition mk_cto_declaration : String.string -> CTO.cto_declaration_kind -> CTO.cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : String.string -> list EImport.import_decl -> list CTO.cto_declaration -> CTO.cto_package
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
  Definition ergo_stmt : Set 
    := Ergo.ergo_stmt.

  Definition evar : String.string -> ergo_expr
    := Ergo.EVar.

  Definition ecasedata : Data.data -> EPattern.ergo_pattern := EPattern.CaseData.
  Definition ecasewildcard : EPattern.type_annotation -> EPattern.ergo_pattern := EPattern.CaseWildcard.
  Definition ecaselet : String.string -> EPattern.type_annotation -> EPattern.ergo_pattern := EPattern.CaseLet.
  Definition ecaseletoption : String.string -> EPattern.type_annotation -> EPattern.ergo_pattern := EPattern.CaseLetOption.

  Definition econst : Data.data -> ergo_expr := Ergo.EConst.
  Definition earray : list ergo_expr -> ergo_expr := Ergo.EArray.
  Definition eunaryop : Ops.Unary.op -> ergo_expr -> ergo_expr
    := Ergo.EUnaryOp.
  Definition ebinaryop : Ops.Binary.op -> ergo_expr -> ergo_expr -> ergo_expr 
    := Ergo.EBinaryOp.
  Definition eif : ergo_expr -> ergo_expr -> ergo_expr -> ergo_expr 
    := Ergo.EIf.
  Definition elet (v:String.string) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.ELet v None e1 e2.
  Definition elet_typed (v:String.string) (t:CTO.cto_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.ELet v (Some t) e1 e2.
  Definition eforeach : list (String.string * ergo_expr) -> option ergo_expr -> ergo_expr -> ergo_expr
    := Ergo.EForeach.
  Definition ecallfun : String.string -> list ergo_expr -> ergo_expr
    := Ergo.ECallFun.
  Definition ematch : ergo_expr -> list (EPattern.ergo_pattern * ergo_expr) -> ergo_expr -> ergo_expr
    := Ergo.EMatch.
  Definition erecord : list (String.string * ergo_expr) -> ergo_expr 
    := Ergo.ERecord.

  Definition sreturn : ergo_expr -> ergo_stmt :=
    Ergo.SReturn.
  Definition sfunreturn : ergo_expr -> ergo_stmt :=
    Ergo.SFunReturn.
  Definition sreturnempty : ergo_stmt :=
    ErgoSugar.SReturnEmpty.
  Definition sfunreturnempty : ergo_stmt :=
    ErgoSugar.SFunReturnEmpty.
  Definition sthrow : ergo_expr -> ergo_stmt :=
    Ergo.SThrow.
  Definition scallclause : String.string -> list ergo_expr -> ergo_stmt
    := Ergo.SCallClause.
  Definition ssetstate : ergo_expr -> ergo_stmt -> ergo_stmt :=
    Ergo.SSetState.
  Definition semit : ergo_expr -> ergo_stmt -> ergo_stmt :=
    Ergo.SEmit.
  Definition slet (v:String.string) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt
    := Ergo.SLet v None e1 s2.
  Definition slet_typed (v:String.string) (t:CTO.cto_type) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt
    := Ergo.SLet v (Some t) e1 s2.
  Definition sif : ergo_expr -> ergo_stmt -> ergo_stmt -> ergo_stmt :=
    Ergo.SIf.
  Definition senforce (e1:ergo_expr) (s2: option ergo_stmt) (s3:ergo_stmt) : ergo_stmt
    := Ergo.SEnforce e1 s2 s3.
  Definition smatch : ergo_expr -> list (EPattern.ergo_pattern * ergo_stmt) -> ergo_stmt -> ergo_stmt
    := Ergo.SMatch.
  
  Definition edot : String.string -> ergo_expr -> ergo_expr 
    := ErgoSugar.EDot.
  Definition enew : option String.string -> String.string -> list (String.string * ergo_expr) -> ergo_expr 
    := ErgoSugar.ENewSugar.
  Definition ethis_contract : ergo_expr
    := Ergo.EThisContract.
  Definition ethis_clause : ergo_expr
    := Ergo.EThisClause.
  Definition ethis_state : ergo_expr
    := Ergo.EThisState.
  Definition elifterror : ergo_expr -> ergo_expr -> ergo_expr
    := Ergo.ELiftError.

  Definition eoptionaldot : String.string -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDot.
  Definition eoptionaldefault : ergo_expr -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDefault.
  
  (** Compilation *)
  Definition ergo_package_to_javascript :
    list CTO.cto_package
    -> ergo_package
    -> EResult.eresult JavaScript.javascript
    := ErgotoJavaScript.ergo_package_to_javascript.

  Definition ergo_package_to_javascript_cicero :
    list CTO.cto_package
    -> ergo_package
    -> EResult.eresult JavaScript.javascript
    := ErgotoJavaScriptCicero.ergo_package_to_javascript_cicero.

  Definition ergo_package_to_java :
    list CTO.cto_package
    -> ergo_package
    -> EResult.eresult Java.java
    := ErgotoJava.ergo_package_to_java.

End ErgoCompiler.

