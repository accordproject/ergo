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
Require Qcert.Common.Brands.BrandRelation.

Require ErgoSpec.Version.
Require ErgoSpec.Backend.ErgoBackend.
Require ErgoSpec.Common.Utils.EProvenance.
Require ErgoSpec.Common.Utils.ENames.
Require ErgoSpec.Common.Utils.EResult.
Require ErgoSpec.Common.Utils.EAstUtil.
Require ErgoSpec.Common.CTO.CTO.
Require ErgoSpec.Common.Types.ErgoType.
Require ErgoSpec.Common.Pattern.EPattern.
Require ErgoSpec.Ergo.Lang.Ergo.
Require ErgoSpec.Ergo.Lang.ErgoSugar.
Require ErgoSpec.Compiler.ErgoDriver.

Module ErgoCompiler.

  Definition ergo_version := Version.ergo_version.
  
  Module ErgoData := ErgoBackend.ErgoData.
  Module ErgoOps := ErgoBackend.ErgoOps.

  (** Utils *)
  (* XXX Exposed so it can be called from JavaScript - Should be removed once we switch to the REPL *)
  Definition javascript_identifier_sanitizer := ErgoBackend.ErgoCodeGen.javascript_identifier_sanitizer.
  
  (** Location *)
  Definition location := EProvenance.location.
  Definition provenance := EProvenance.provenance.

  Definition loc_of_provenance := EProvenance.loc_of_provenance.
  
  Definition prov_func := EProvenance.ProvFunc.
  Definition prov_clause := EProvenance.ProvClause.
  Definition prov_this_contract := EProvenance.ProvThisContract.
  Definition prov_this_clause := EProvenance.ProvThisClause.
  Definition prov_this_state := EProvenance.ProvThisState.
  Definition prov_loc := EProvenance.ProvLoc.

  (** Names *)
  Definition relative_name : Set := ENames.relative_name.

  (** Results *)
  Definition eerror : Set := EResult.eerror.
  Definition system_error : provenance -> String.string -> eerror := EResult.ESystemError.
  Definition parse_error : provenance -> String.string -> eerror := EResult.EParseError.
  Definition compilation_error : provenance -> String.string -> eerror := EResult.ECompilationError.
  Definition type_error : provenance -> String.string -> eerror := EResult.ETypeError.
  Definition runtime_error : provenance -> String.string -> eerror := EResult.ERuntimeError.

  Definition eresult (A:Set) : Set := EResult.eresult A.
  Definition esuccess (A:Set) : A -> eresult A := EResult.esuccess.
  Definition efailure (A:Set) : eerror -> eresult A := EResult.efailure.

  (** CTOs *)
  Definition cto_type := CTO.lrcto_type.
  Definition cto_declaration_desc := CTO.lrcto_declaration_desc.
  Definition cto_declaration := CTO.lrcto_declaration.
  Definition cto_package := CTO.lrcto_package.
  
  Definition cto_boolean : provenance -> cto_type
    := CTO.CTOBoolean.
  Definition cto_string : provenance -> cto_type
    := CTO.CTOString.
  Definition cto_double : provenance -> cto_type
    := CTO.CTODouble.
  Definition cto_long : provenance -> cto_type
    := CTO.CTOLong.
  Definition cto_integer : provenance -> cto_type
    := CTO.CTOInteger.
  Definition cto_dateTime : provenance -> cto_type
    := CTO.CTODateTime.
  Definition cto_class_ref prov name_ref : cto_type
    := CTO.CTOClassRef prov name_ref.
  Definition cto_option prov ct : cto_type
    := CTO.CTOOption prov ct.
  Definition cto_array prov ct : cto_type
    := CTO.CTOArray prov ct.

  Definition cto_enum : list String.string -> cto_declaration_desc
    := CTO.CTOEnum.
  Definition cto_transaction : option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOTransaction.
  Definition cto_concept : option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOConcept.

  Definition mk_cto_declaration : EProvenance.provenance -> String.string -> cto_declaration_desc -> cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package : EProvenance.provenance -> String.string -> list EAstUtil.import_decl -> list cto_declaration -> cto_package
    := CTO.mkCTOPackage.

  (** Types *)
  Definition ergo_type : Set
    := ErgoType.lrergo_type.
  Definition ergo_type_declaration_desc : Set :=
    ErgoType.lrergo_type_declaration_desc.
  Definition ergo_type_declaration : Set :=
    ErgoType.lrergo_type_declaration.
  
  Definition ergo_type_any prov : ergo_type
    := ErgoType.ErgoTypeAny prov.
  Definition ergo_type_none prov : ergo_type
    := ErgoType.ErgoTypeNone prov.
  Definition ergo_type_boolean prov : ergo_type
    := ErgoType.ErgoTypeBoolean prov.
  Definition ergo_type_string prov : ergo_type
    := ErgoType.ErgoTypeString prov.
  Definition ergo_type_double prov : ergo_type
    := ErgoType.ErgoTypeDouble prov.
  Definition ergo_type_long prov : ergo_type
    := ErgoType.ErgoTypeLong prov.
  Definition ergo_type_integer prov : ergo_type
    := ErgoType.ErgoTypeInteger prov.
  Definition ergo_type_dateTime prov : ergo_type
    := ErgoType.ErgoTypeDateTime prov.
  Definition ergo_type_class_ref prov relative_name : ergo_type
    := ErgoType.ErgoTypeClassRef prov relative_name.
  Definition ergo_type_option prov et : ergo_type
    := ErgoType.ErgoTypeOption prov et.
  Definition ergo_type_record prov rec : ergo_type
    := ErgoType.ErgoTypeRecord prov rec.
  Definition ergo_type_array prov et : ergo_type
    := ErgoType.ErgoTypeArray prov et.

  Definition ergo_type_enum : list String.string -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeEnum.
  Definition ergo_type_transaction : option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeTransaction.
  Definition ergo_type_concept : option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeConcept.

  Definition mk_ergo_type_declaration : EProvenance.provenance -> String.string -> ergo_type_declaration_desc -> ergo_type_declaration
    := ErgoType.mkErgoTypeDeclaration.

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
  Definition ergo_input : Set 
    := Ergo.lrergo_input.

  (** Patterns *)
  Definition ecasedata : EProvenance.provenance -> ErgoData.data -> EPattern.lrergo_pattern
    := EPattern.CaseData.
  Definition ecasewildcard : EProvenance.provenance -> EPattern.type_annotation -> EPattern.lrergo_pattern
    := EPattern.CaseWildcard.
  Definition ecaselet : EProvenance.provenance -> String.string -> EPattern.type_annotation -> EPattern.lrergo_pattern
    := EPattern.CaseLet.
  Definition ecaseletoption : EProvenance.provenance -> String.string -> EPattern.type_annotation -> EPattern.lrergo_pattern
    := EPattern.CaseLetOption.

  (** Expressions *)
  Definition ethis_contract prov : ergo_expr
    := Ergo.EThisContract prov.
  Definition ethis_clause prov : ergo_expr
    := Ergo.EThisClause prov.
  Definition ethis_state prov : ergo_expr
    := Ergo.EThisState prov.
  Definition evar prov v: ergo_expr
    := Ergo.EVar prov v.
  Definition econst prov d :ergo_expr
    := Ergo.EConst prov d.
  Definition earray prov arr : ergo_expr
    := Ergo.EArray prov arr.
  Definition eunaryop prov u e : ergo_expr
    := Ergo.EUnaryOp prov u e.
  Definition ebinaryop prov b e1 e2 : ergo_expr 
    := Ergo.EBinaryOp prov b e1 e2.
  Definition eif prov e1 e2 e3 : ergo_expr 
    := Ergo.EIf prov e1 e2 e3.
  Definition elet prov (v:String.string) (t:option ErgoType.ergo_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.ELet prov v t e1 e2.
  Definition enew prov n rec : ergo_expr 
    := Ergo.ENew prov n rec.
  Definition erecord prov rec : ergo_expr 
    := Ergo.ERecord prov rec.
  Definition ecallfun prov f el : ergo_expr
    := Ergo.ECallFun prov f el.
  Definition ematch prov e0 epl ed : ergo_expr
    := Ergo.EMatch prov e0 epl ed.
  Definition eforeach prov efl ew er : ergo_expr
    := Ergo.EForeach prov efl ew er.

  Section Integer.
    Local Open Scope Z_scope.
    (* XXX missing unary operator in Q*cert *)
    Definition opuminusi prov e :=
      ebinaryop prov ErgoOps.Binary.Integer.opminusi (econst prov (ErgoData.dnat 0)) e.
  End Integer.
  
  (** Statements *)
  Definition sreturn prov e : ergo_stmt :=
    Ergo.SReturn prov e.
  Definition efunreturn (prov:provenance) e : ergo_expr := e.
  Definition sthrow prov e : ergo_stmt :=
    Ergo.SThrow prov e.
  Definition scallclause prov e0 c el : ergo_stmt :=
    Ergo.SCallClause prov e0 c el.
  Definition ssetstate prov e s : ergo_stmt :=
    Ergo.SSetState prov e s.
  Definition semit prov e s : ergo_stmt :=
    Ergo.SEmit prov e s.
  Definition slet prov (v:String.string) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SLet prov v None e1 s2.
  Definition slet_typed prov (v:String.string) (t:ErgoType.ergo_type) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SLet prov v (Some t) e1 s2.
  Definition sif prov e1 s2 s3 : ergo_stmt :=
    Ergo.SIf prov e1 s2 s3.
  Definition senforce prov (e1:ergo_expr) (s2: option ergo_stmt) (s3:ergo_stmt) : ergo_stmt :=
    Ergo.SEnforce prov e1 s2 s3.
  Definition smatch prov e slp sd : ergo_stmt :=
    Ergo.SMatch prov e slp sd.

  (** Syntactic sugar *)
  Definition edot : EProvenance.provenance -> String.string -> ergo_expr -> ergo_expr 
    := ErgoSugar.EDot.
  Definition eoptionaldot : EProvenance.provenance -> String.string -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDot.
  Definition eoptionaldefault : EProvenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDefault.
  Definition sreturnempty : EProvenance.provenance -> ergo_stmt :=
    ErgoSugar.SReturnEmpty.
  Definition efunreturnempty : EProvenance.provenance -> ergo_expr :=
    ErgoSugar.EFunReturnEmpty.
  
  (** Declarations *)
  Definition dimport prov id : ergo_declaration
    := Ergo.DImport prov id.
  Definition dtype prov etd : ergo_declaration
    := Ergo.DType prov etd.
  Definition dstmt prov s : ergo_declaration
    := Ergo.DStmt prov s.
  Definition dconstant prov v e : ergo_declaration
    := Ergo.DConstant prov v e.
  Definition dfunc prov fn f : ergo_declaration
    := Ergo.DFunc prov fn f.
  Definition dcontract prov cn c : ergo_declaration
    := Ergo.DContract prov cn c.
  Definition dsetcontract prov cn e : ergo_declaration
    := Ergo.DSetContract prov cn e.

  (** Compilation *)
  Definition ergo_module_to_javascript :
    list CTO.cto_package
    -> list ergo_module
    -> ergo_module
    -> EResult.eresult JavaScript.javascript
    := ErgoDriver.ergo_module_to_javascript_top.

  Definition ergo_module_to_javascript_cicero :
    list CTO.cto_package
    -> list ergo_module
    -> ergo_module
    -> EResult.eresult JavaScript.javascript
    := ErgoDriver.ergo_module_to_javascript_cicero_top.

  Definition ergo_module_to_java :
    list CTO.cto_package
    -> list ergo_module
    -> ergo_module
    -> EResult.eresult Java.java
    := ErgoDriver.ergo_module_to_java_top.

  Definition test_brand_model := ErgoCType.StoreBrandModel.
  Definition test_brand_relation := ErgoCType.StoreBrandRelation.

  (** REPL *)
  Definition init_repl_context :
    list CTO.cto_package
    -> list ergo_module
    -> EResult.eresult ErgoDriver.repl_context
    := @ErgoDriver.init_repl_context test_brand_model.
  Definition ergo_repl_eval_decl :
    ErgoDriver.repl_context
    -> ergo_declaration
    -> EResult.eresult String.string * ErgoDriver.repl_context
    := @ErgoDriver.ergo_repl_eval_decl test_brand_model.

End ErgoCompiler.

