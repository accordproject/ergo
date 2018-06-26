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
Require ErgoSpec.Common.Utils.EAstUtil.
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

  (** Utils *)
  (* XXX Exposed so it can be called from JavaScript - Should be removed once we switch to the REPL *)
  Definition javascript_identifier_sanitizer := ErgoBackend.ErgoCodeGen.javascript_identifier_sanitizer.
  
  (** Location *)
  Definition location := EResult.location.

  (** Names *)
  Definition relative_name : Set := ENames.relative_name.

  (** CTOs *)
  Definition cto_type := CTO.lrcto_type.
  Definition cto_declaration_desc := CTO.lrcto_declaration_desc.
  Definition cto_declaration := CTO.lrcto_declaration.
  Definition cto_package := CTO.lrcto_package.
  
  Definition cto_boolean : location -> cto_type
    := CTO.CTOBoolean.
  Definition cto_string : location -> cto_type
    := CTO.CTOString.
  Definition cto_double : location -> cto_type
    := CTO.CTODouble.
  Definition cto_long : location -> cto_type
    := CTO.CTOLong.
  Definition cto_integer : location -> cto_type
    := CTO.CTOInteger.
  Definition cto_dateTime : location -> cto_type
    := CTO.CTODateTime.
  Definition cto_class_ref loc name_ref : cto_type
    := CTO.CTOClassRef loc name_ref.
  Definition cto_option loc ct : cto_type
    := CTO.CTOOption loc ct.
  Definition cto_array loc ct : cto_type
    := CTO.CTOArray loc ct.

  Definition cto_enum : list String.string -> cto_declaration_desc
    := CTO.CTOEnum.
  Definition cto_transaction : option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOTransaction.
  Definition cto_concept : option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOConcept.

  Definition mk_cto_declaration : EResult.location -> String.string -> cto_declaration_desc -> cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : EResult.location -> String.string -> list EAstUtil.import_decl -> list cto_declaration -> cto_package
    := CTO.mkCTOPackage.

  (** Types *)
  Definition ergo_type : Set
    := ErgoType.lrergo_type.
  Definition ergo_type_declaration_desc : Set :=
    ErgoType.lrergo_type_declaration_desc.
  Definition ergo_type_declaration : Set :=
    ErgoType.lrergo_type_declaration.
  Definition ergo_type_module : Set :=
    ErgoType.lrergo_type_module.
  
  Definition ergo_type_any loc : ergo_type
    := ErgoType.ErgoTypeAny loc.
  Definition ergo_type_none loc : ergo_type
    := ErgoType.ErgoTypeNone loc.
  Definition ergo_type_boolean loc : ergo_type
    := ErgoType.ErgoTypeBoolean loc.
  Definition ergo_type_string loc : ergo_type
    := ErgoType.ErgoTypeString loc.
  Definition ergo_type_double loc : ergo_type
    := ErgoType.ErgoTypeDouble loc.
  Definition ergo_type_long loc : ergo_type
    := ErgoType.ErgoTypeLong loc.
  Definition ergo_type_integer loc : ergo_type
    := ErgoType.ErgoTypeInteger loc.
  Definition ergo_type_dateTime loc : ergo_type
    := ErgoType.ErgoTypeDateTime loc.
  Definition ergo_type_class_ref loc relative_name : ergo_type
    := ErgoType.ErgoTypeClassRef loc relative_name.
  Definition ergo_type_option loc et : ergo_type
    := ErgoType.ErgoTypeOption loc et.
  Definition ergo_type_record loc rec : ergo_type
    := ErgoType.ErgoTypeRecord loc rec.
  Definition ergo_type_array loc et : ergo_type
    := ErgoType.ErgoTypeArray loc et.

  Definition ergo_type_enum : list String.string -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeEnum.
  Definition ergo_type_transaction : option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeTransaction.
  Definition ergo_type_concept : option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeConcept.

  Definition mk_ergo_type_declaration : EResult.location -> String.string -> ergo_type_declaration_desc -> ergo_type_declaration
    := ErgoType.mkErgoTypeDeclaration.
  Definition mk_ergo_type_module : EResult.location -> String.string -> list EAstUtil.import_decl -> list ergo_type_declaration -> ergo_type_module
    := ErgoType.mkErgoTypeModule.

  (** Ergo *)
  Definition ergo_expr : Set 
    := Ergo.lrergo_expr.
  Definition ergo_stmt : Set 
    := Ergo.lrergo_stmt.
  Definition ergo_function : Set
    := Ergo.lrergo_function.
  Definition ergo_clause : Set
    := Ergo.lrergo_clause.
  Definition ergo_declaration : Set
    := Ergo.lrergo_declaration.
  Definition ergo_contract : Set
    := Ergo.lrergo_contract.
  Definition ergo_module : Set 
    := Ergo.lrergo_module.

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
    := Ergo.EThisContract loc.
  Definition ethis_clause loc : ergo_expr
    := Ergo.EThisClause loc.
  Definition ethis_state loc : ergo_expr
    := Ergo.EThisState loc.
  Definition evar loc v: ergo_expr
    := Ergo.EVar loc v.
  Definition econst loc d :ergo_expr
    := Ergo.EConst loc d.
  Definition earray loc arr : ergo_expr
    := Ergo.EArray loc arr.
  Definition eunaryop loc u e : ergo_expr
    := Ergo.EUnaryOp loc u e.
  Definition ebinaryop loc b e1 e2 : ergo_expr 
    := Ergo.EBinaryOp loc b e1 e2.
  Definition eif loc e1 e2 e3 : ergo_expr 
    := Ergo.EIf loc e1 e2 e3.
  Definition elet loc (v:String.string) (t:option ErgoType.ergo_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.ELet loc v t e1 e2.
  Definition enew loc n rec : ergo_expr 
    := Ergo.ENew loc n rec.
  Definition erecord loc rec : ergo_expr 
    := Ergo.ERecord loc rec.
  Definition ecallfun loc f el : ergo_expr
    := Ergo.ECallFun loc f el.
  Definition ematch loc e0 epl ed : ergo_expr
    := Ergo.EMatch loc e0 epl ed.
  Definition eforeach loc efl ew er : ergo_expr
    := Ergo.EForeach loc efl ew er.

  (** Statements *)
  Definition sreturn loc e : ergo_stmt :=
    Ergo.SReturn loc e.
  Definition sfunreturn loc e : ergo_stmt :=
    Ergo.SFunReturn loc e.
  Definition sthrow loc e : ergo_stmt :=
    Ergo.SThrow loc e.
  Definition scallclause loc c el : ergo_stmt :=
    Ergo.SCallClause loc c el.
  Definition ssetstate loc e s : ergo_stmt :=
    Ergo.SSetState loc e s.
  Definition semit loc e s : ergo_stmt :=
    Ergo.SEmit loc e s.
  Definition slet loc (v:String.string) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SLet loc v None e1 s2.
  Definition slet_typed loc (v:String.string) (t:ErgoType.ergo_type) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SLet loc v (Some t) e1 s2.
  Definition sif loc e1 s2 s3 : ergo_stmt :=
    Ergo.SIf loc e1 s2 s3.
  Definition senforce loc (e1:ergo_expr) (s2: option ergo_stmt) (s3:ergo_stmt) : ergo_stmt :=
    Ergo.SEnforce loc e1 s2 s3.
  Definition smatch loc e slp sd : ergo_stmt :=
    Ergo.SMatch loc e slp sd.

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
    := Ergo.DType loc etd.
  Definition dstmt loc s : ergo_declaration
    := Ergo.DStmt loc s.
  Definition dconstant loc v e : ergo_declaration
    := Ergo.DConstant loc v e.
  Definition dfunc loc f : ergo_declaration
    := Ergo.DFunc loc f.
  Definition dcontract loc c : ergo_declaration
    := Ergo.DContract loc c.

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

