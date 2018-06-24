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
Require ErgoSpec.Common.Types.ErgoType.
Require ErgoSpec.Common.Pattern.EPattern.
Require ErgoSpec.Ergo.Lang.Ergo.
Require ErgoSpec.Ergo.Lang.ErgoSugar.
Require ErgoSpec.Translation.ErgotoJavaScript.
Require ErgoSpec.Translation.ErgotoJava.
Require ErgoSpec.Translation.ErgotoJavaScriptCicero.

Module ErgoCompiler.

  Definition ergo_version := Version.ergo_version.
  
  Module ErgoData := ErgoBackend.ErgoData.
  Module ErgoOps := ErgoBackend.ErgoOps.

  (** Names *)
  Definition name_ref : Set
    := ENames.name_ref.
  Definition mk_relative_ref : option String.string -> String.string -> name_ref
    := ENames.RelativeRef.
  Definition mk_absolute_ref : String.string -> name_ref
    := ENames.AbsoluteRef.

  (** CTOs *)
  Definition cto_boolean loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTOBoolean.
  Definition cto_string loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTOString.
  Definition cto_double loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTODouble.
  Definition cto_long loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTOLong.
  Definition cto_integer loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTOInteger.
  Definition cto_dateTime loc : CTO.cto_type
    := CTO.mk_cto loc CTO.CTODateTime.
  Definition cto_class_ref loc name_ref : CTO.cto_type
    := CTO.mk_cto loc (CTO.CTOClassRef name_ref).
  Definition cto_option loc ct : CTO.cto_type
    := CTO.mk_cto loc (CTO.CTOOption ct).
  Definition cto_array loc ct : CTO.cto_type
    := CTO.mk_cto loc (CTO.CTOArray ct).

  Definition cto_enum : list String.string -> CTO.cto_declaration_desc
    := CTO.CTOEnum.
  Definition cto_transaction : option name_ref -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_desc
    := CTO.CTOTransaction.
  Definition cto_concept : option name_ref -> list (String.string * CTO.cto_type) -> CTO.cto_declaration_desc
    := CTO.CTOConcept.

  Definition mk_cto_declaration : String.string -> EResult.location -> CTO.cto_declaration_desc -> CTO.cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : String.string -> EResult.location -> list EImport.import_decl -> list CTO.cto_declaration -> CTO.cto_package
    := CTO.mkCTOPackage.

  (** Types *)
  Definition ergo_type : Set 
    := ErgoType.ergo_type.
  Definition ergo_type_any loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeAny.
  Definition ergo_type_none loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeNone.
  Definition ergo_type_boolean loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeBoolean.
  Definition ergo_type_string loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeString.
  Definition ergo_type_double loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeDouble.
  Definition ergo_type_long loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeLong.
  Definition ergo_type_integer loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeInteger.
  Definition ergo_type_dateTime loc : ergo_type
    := ErgoType.mk_type loc ErgoType.ErgoTypeDateTime.
  Definition ergo_type_class_ref loc name_ref : ergo_type
    := ErgoType.mk_type loc (ErgoType.ErgoTypeClassRef name_ref).
  Definition ergo_type_option loc et : ergo_type
    := ErgoType.mk_type loc (ErgoType.ErgoTypeOption et).
  Definition ergo_type_record loc rec : ergo_type
    := ErgoType.mk_type loc (ErgoType.ErgoTypeRecord rec).
  Definition ergo_type_array loc et : ergo_type
    := ErgoType.mk_type loc (ErgoType.ErgoTypeArray et).

  Definition ergo_type_enum : list String.string -> ErgoType.ergo_type_declaration_desc
    := ErgoType.ErgoTypeEnum.
  Definition ergo_type_transaction : option name_ref -> list (String.string * ErgoType.ergo_type) -> ErgoType.ergo_type_declaration_desc
    := ErgoType.ErgoTypeTransaction.
  Definition ergo_type_concept : option name_ref -> list (String.string * ErgoType.ergo_type) -> ErgoType.ergo_type_declaration_desc
    := ErgoType.ErgoTypeConcept.

  Definition mk_ergo_type_declaration : String.string -> EResult.location -> ErgoType.ergo_type_declaration_desc -> ErgoType.ergo_type_declaration
    := ErgoType.mkErgoTypeDeclaration.
  Definition mk_ergo_type_module : String.string -> EResult.location -> list EImport.import_decl -> list ErgoType.ergo_type_declaration -> ErgoType.ergo_type_module
    := ErgoType.mkErgoTypeModule.

  (** Ergo *)
  Definition ergo_expr : Set 
    := Ergo.ergo_expr.
  Definition ergo_stmt : Set 
    := Ergo.ergo_stmt.
  Definition ergo_function : Set
    := Ergo.ergo_function.
  Definition ergo_clause : Set
    := Ergo.ergo_clause.
  Definition ergo_declaration : Set
    := Ergo.ergo_declaration.
  Definition ergo_module : Set 
    := Ergo.ergo_module.
  Definition ergo_contract : Set
    := Ergo.ergo_contract.

  (** Patterns *)
  Definition ecasedata : ErgoData.data -> EPattern.ergo_pattern
    := EPattern.CaseData.
  Definition ecasewildcard : EPattern.type_annotation -> EPattern.ergo_pattern
    := EPattern.CaseWildcard.
  Definition ecaselet : String.string -> EPattern.type_annotation -> EPattern.ergo_pattern
    := EPattern.CaseLet.
  Definition ecaseletoption : String.string -> EPattern.type_annotation -> EPattern.ergo_pattern
    := EPattern.CaseLetOption.

  (** Expressions *)
  Definition ethis_contract loc : ergo_expr
    := Ergo.mk_expr loc Ergo.EThisContract.
  Definition ethis_clause loc : ergo_expr
    := Ergo.mk_expr loc Ergo.EThisClause.
  Definition ethis_state loc : ergo_expr
    := Ergo.mk_expr loc Ergo.EThisState.
  Definition evar loc v: ergo_expr
    := Ergo.mk_expr loc (Ergo.EVar v).
  Definition econst loc d :ergo_expr
    := Ergo.mk_expr loc (Ergo.EConst d).
  Definition earray loc arr : ergo_expr
    := Ergo.mk_expr loc (Ergo.EArray arr).
  Definition eunaryop loc u e : ergo_expr
    := Ergo.mk_expr loc (Ergo.EUnaryOp u e).
  Definition ebinaryop loc b e1 e2 : ergo_expr 
    := Ergo.mk_expr loc (Ergo.EBinaryOp b e1 e2).
  Definition eif loc e1 e2 e3 : ergo_expr 
    := Ergo.mk_expr loc (Ergo.EIf e1 e2 e3).
  Definition elet loc (v:String.string) (t:option ErgoType.ergo_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.mk_expr loc (Ergo.ELet v t e1 e2).
  Definition enew loc n rec : ergo_expr 
    := Ergo.mk_expr loc (Ergo.ENew n rec).
  Definition erecord loc rec : ergo_expr 
    := Ergo.mk_expr loc (Ergo.ERecord rec).
  Definition ecallfun loc f el : ergo_expr
    := Ergo.mk_expr loc (Ergo.ECallFun f el).
  Definition ematch loc e0 epl ed : ergo_expr
    := Ergo.mk_expr loc (Ergo.EMatch e0 epl ed).
  Definition eforeach loc efl ew er : ergo_expr
    := Ergo.mk_expr loc (Ergo.EForeach efl ew er).

  (** Statements *)
  Definition sreturn loc e : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SReturn e).
  Definition sfunreturn loc e : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SFunReturn e).
  Definition sthrow loc e : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SThrow e).
  Definition scallclause loc c el : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SCallClause c el).
  Definition ssetstate loc e s : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SSetState  e s).
  Definition semit loc e s : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SEmit e s).
  Definition slet loc (v:String.string) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SLet v None e1 s2).
  Definition slet_typed loc (v:String.string) (t:ErgoType.ergo_type) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SLet v (Some t) e1 s2).
  Definition sif loc e1 s2 s3 : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SIf e1 s2 s3).
  Definition senforce loc (e1:ergo_expr) (s2: option ergo_stmt) (s3:ergo_stmt) : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SEnforce e1 s2 s3).
  Definition smatch loc e slp sd : ergo_stmt :=
    Ergo.mk_stmt loc (Ergo.SMatch e slp sd).

  (** Syntactic sugar *)
  Definition edot : EResult.location -> String.string -> ergo_expr -> ergo_expr 
    := ErgoSugar.EDot.
  Definition eoptionaldot : EResult.location -> String.string -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDot.
  Definition eoptionaldefault : EResult.location -> ergo_expr -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDefault.
  Definition sreturnempty : EResult.location -> ergo_stmt :=
    ErgoSugar.SReturnEmpty.
  Definition sfunreturnempty : EResult.location -> ergo_stmt :=
    ErgoSugar.SFunReturnEmpty.
  
  (** Declarations *)
  Definition dtype loc etd : ergo_declaration
    := Ergo.mk_decl loc (Ergo.DType etd).
  Definition dstmt loc s : ergo_declaration
    := Ergo.mk_decl loc (Ergo.DStmt s).
  Definition dconstant loc v e : ergo_declaration
    := Ergo.mk_decl loc (Ergo.DConstant v e).
  Definition dfunc loc f : ergo_declaration
    := Ergo.mk_decl loc (Ergo.DFunc f).
  Definition dcontract loc c : ergo_declaration
    := Ergo.mk_decl loc (Ergo.DContract c).

  (** Compilation *)
  Definition ergo_module_to_javascript :
    list CTO.cto_package
    -> ergo_module
    -> EResult.eresult JavaScript.javascript
    := ErgotoJavaScript.ergo_module_to_javascript.

  Definition ergo_module_to_javascript_cicero :
    list CTO.cto_package
    -> ergo_module
    -> EResult.eresult JavaScript.javascript
    := ErgotoJavaScriptCicero.ergo_module_to_javascript_cicero.

  Definition ergo_module_to_java :
    list CTO.cto_package
    -> ergo_module
    -> EResult.eresult Java.java
    := ErgotoJava.ergo_module_to_java.

End ErgoCompiler.

