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
Require ErgoSpec.Utils.Misc.
Require ErgoSpec.Backend.ErgoBackend.
Require ErgoSpec.Common.Provenance.
Require ErgoSpec.Common.Names.
Require ErgoSpec.Common.Result.
Require ErgoSpec.Common.Ast.
Require ErgoSpec.Types.CTO.
Require ErgoSpec.Types.ErgoType.
Require ErgoSpec.Ergo.Lang.Ergo.
Require ErgoSpec.Ergo.Lang.ErgoSugar.
Require ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require ErgoSpec.Compiler.ErgoDriver.

Module ErgoCompiler.

  Definition ergo_version := Version.ergo_version.
  
  Module ErgoData := ErgoBackend.ErgoData.
  Module ErgoOps := ErgoBackend.ErgoOps.
  Module ErgoCType := ErgoBackend.ErgoCType.

  (** Utils *)
  (* XXX Exposed so it can be called from JavaScript - Should be removed once we switch to the REPL *)
  Definition javascript_identifier_sanitizer := ErgoBackend.ErgoCodeGen.javascript_identifier_sanitizer.

  (** Location *)
  Definition location := Provenance.location.
  Definition provenance := Provenance.provenance.

  Definition loc_of_provenance := Provenance.loc_of_provenance.
  
  Definition prov_func := Provenance.ProvFunc.
  Definition prov_clause := Provenance.ProvClause.
  Definition prov_this_contract := Provenance.ProvThisContract.
  Definition prov_this_clause := Provenance.ProvThisClause.
  Definition prov_this_state := Provenance.ProvThisState.
  Definition prov_loc := Provenance.ProvLoc.

  (** Names *)
  Definition relative_name : Set := Names.relative_name.

  (** Results *)
  Definition eerror : Set := Result.eerror.
  Definition ewarning : Set := Result.ewarning.
  Definition system_error : provenance -> String.string -> eerror := Result.ESystemError.
  Definition parse_error : provenance -> String.string -> eerror := Result.EParseError.
  Definition compilation_error : provenance -> String.string -> eerror := Result.ECompilationError.
  Definition type_error : provenance -> String.string -> eerror := Result.ETypeError.
  Definition runtime_error : provenance -> String.string -> eerror := Result.ERuntimeError.

  Definition eresult (A:Set) : Set := Result.eresult A.
  Definition esuccess (A:Set) : A -> list ewarning -> eresult A := Result.esuccess.
  Definition efailure (A:Set) : eerror -> eresult A := Result.efailure.

  Definition result_file : Set := ErgoNNRC.result_file.
  
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
  Definition cto_transaction :
    bool -> option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOTransaction.
  Definition cto_concept :
    bool -> option relative_name -> list (String.string * cto_type) -> cto_declaration_desc
    := CTO.CTOConcept.

  Definition mk_cto_declaration :
    Provenance.provenance -> String.string -> cto_declaration_desc -> cto_declaration
    := CTO.mkCTODeclaration.
  Definition mk_cto_package :
    Provenance.provenance
    -> String.string
    -> String.string
    -> String.string
    -> list Ast.import_decl
    -> list cto_declaration
    -> cto_package
    := CTO.mkCTOPackage.

  (** Types *)
  Definition ergo_type : Set
    := ErgoType.lrergo_type.
  Definition ergo_type_declaration_desc : Set :=
    ErgoType.lrergo_type_declaration_desc.
  Definition ergo_type_declaration : Set :=
    ErgoType.lrergo_type_declaration.
  Definition laergo_type_declaration : Set :=
    ErgoType.laergo_type_declaration.
  
  Definition ergo_type_any prov : ergo_type
    := ErgoType.ErgoTypeAny prov.
  Definition ergo_type_nothing prov : ergo_type
    := ErgoType.ErgoTypeNothing prov.
  Definition ergo_type_unit prov : ergo_type
    := ErgoType.ErgoTypeUnit prov.
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
  Definition ergo_type_duration prov : ergo_type
    := ErgoType.ErgoTypeDuration prov.
  Definition ergo_type_period prov : ergo_type
    := ErgoType.ErgoTypePeriod prov.
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
  Definition ergo_type_transaction :
    bool -> option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeTransaction.
  Definition ergo_type_concept :
    bool -> option relative_name -> list (String.string * ergo_type) -> ergo_type_declaration_desc
    := ErgoType.ErgoTypeConcept.

  Definition mk_ergo_type_declaration :
    Provenance.provenance -> String.string -> ergo_type_declaration_desc -> ergo_type_declaration
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
  Definition ecasedata : Provenance.provenance -> ErgoData.data -> Ast.lrergo_pattern
    := Ast.CaseData.
  Definition ecasewildcard : Provenance.provenance -> Ast.type_annotation -> Ast.lrergo_pattern
    := Ast.CaseWildcard.
  Definition ecaselet : Provenance.provenance -> String.string -> Ast.type_annotation -> Ast.lrergo_pattern
    := Ast.CaseLet.
  Definition ecaseletoption : Provenance.provenance -> String.string -> Ast.type_annotation -> Ast.lrergo_pattern
    := Ast.CaseLetOption.

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
  Definition enone prov : ergo_expr
    := Ergo.ENone prov.
  Definition esome prov : ergo_expr -> ergo_expr
    := Ergo.ESome prov.
  Definition earray prov arr : ergo_expr
    := Ergo.EArray prov arr.
  Definition eunaryoperator prov b e : ergo_expr 
    := Ergo.EUnaryOperator prov b e.
  Definition ebinaryoperator prov b e1 e2 : ergo_expr 
    := Ergo.EBinaryOperator prov b e1 e2.
  Definition eunarybuiltin prov u e : ergo_expr
    := Ergo.EUnaryBuiltin prov u e.
  Definition ebinarybuiltin prov b e1 e2 : ergo_expr 
    := Ergo.EBinaryBuiltin prov b e1 e2.
  Definition eif prov e1 e2 e3 : ergo_expr 
    := Ergo.EIf prov e1 e2 e3.
  Definition elet prov (v:String.string) (t:option ErgoType.ergo_type) (e1 e2:ergo_expr) : ergo_expr
    := Ergo.ELet prov v t e1 e2.
  Definition eprint prov (e1 e2:ergo_expr) : ergo_expr
    := Ergo.EPrint prov e1 e2.
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
      ebinarybuiltin prov ErgoOps.Binary.Integer.opminusi (econst prov (ErgoData.dnat 0)) e.
  End Integer.
  
  (** Statements *)
  Definition sreturn prov e : ergo_stmt :=
    Ergo.SReturn prov e.
  Definition efunreturn (prov:provenance) e : ergo_expr := e.
  Definition sthrow prov e : ergo_stmt :=
    Ergo.SThrow prov e.
  Definition scallclause prov e0 c el : ergo_stmt :=
    Ergo.SCallClause prov e0 c el.
  Definition scallcontract prov (e0 e1:ergo_expr) : ergo_stmt :=
    Ergo.SCallContract prov e0 (e1::nil).
  Definition ssetstate prov e s : ergo_stmt :=
    Ergo.SSetState prov e s.
  Definition semit prov e s : ergo_stmt :=
    Ergo.SEmit prov e s.
  Definition slet prov (v:String.string) (t:option ErgoType.ergo_type) (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SLet prov v t e1 s2.
  Definition sprint prov (e1:ergo_expr) (s2:ergo_stmt) : ergo_stmt :=
    Ergo.SPrint prov e1 s2.
  Definition sif prov e1 s2 s3 : ergo_stmt :=
    Ergo.SIf prov e1 s2 s3.
  Definition senforce prov (e1:ergo_expr) (s2: option ergo_stmt) (s3:ergo_stmt) : ergo_stmt :=
    Ergo.SEnforce prov e1 s2 s3.
  Definition smatch prov e slp sd : ergo_stmt :=
    Ergo.SMatch prov e slp sd.

  (** Syntactic sugar *)
  Definition eoptionaldot : Provenance.provenance -> String.string -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDot.
  Definition eoptionaldefault : Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr
    := ErgoSugar.EOptionalDefault.
  Definition sreturnempty : Provenance.provenance -> ergo_stmt :=
    ErgoSugar.SReturnEmpty.
  Definition efunreturnempty : Provenance.provenance -> ergo_expr :=
    ErgoSugar.EFunReturnEmpty.
  
  (** Declarations *)
  Definition dnamespace prov ns : ergo_declaration
    := Ergo.DNamespace prov ns.
  Definition dimport prov id : ergo_declaration
    := Ergo.DImport prov id.
  Definition dtype prov etd : ergo_declaration
    := Ergo.DType prov etd.
  Definition dstmt prov s : ergo_declaration
    := Ergo.DStmt prov s.
  Definition dconstant prov v ta e : ergo_declaration
    := Ergo.DConstant prov v ta e.
  Definition dfunc prov fn f : ergo_declaration
    := Ergo.DFunc prov fn f.
  Definition dcontract prov cn c : ergo_declaration
    := Ergo.DContract prov cn c.
  Definition dsetcontract prov cn e : ergo_declaration
    := Ergo.DSetContract prov cn e.

  (** Compilation *)
  Definition ergo_module_to_javascript :
    Misc.jsversion
    -> list ergo_input
    -> Result.eresult result_file
    := ErgoDriver.ergo_module_to_javascript_top.

  Definition ergo_module_to_cicero :
    list ergo_input
    -> Result.eresult result_file
    := ErgoDriver.ergo_module_to_cicero_top.

  Definition ergo_module_to_java :
    list ergo_input
    -> Result.eresult result_file
    := ErgoDriver.ergo_module_to_java_top.

  (** Brand model *)
  Definition ergo_brand_model := ErgoCType.tbrand_model.

  Definition ergo_empty_brand_model := ErgoCType.tempty_brand_model.

  Definition ergo_brand_model_from_inputs
             (inputs : list ergo_input) : eresult (ergo_brand_model * list laergo_type_declaration)
    := ErgoDriver.brand_model_from_inputs inputs.

  Definition ergo_refresh_brand_model {bm:ergo_brand_model} :
    @ErgoDriver.repl_context bm -> eresult (ergo_brand_model * @ErgoDriver.repl_context bm)
    := ErgoDriver.refresh_brand_model.

  (** REPL *)
  Definition init_repl_context {bm:ergo_brand_model} (inputs:list ergo_input)
    := @ErgoDriver.init_repl_context bm inputs.

  Definition ergo_repl_eval_decl {bm:ergo_brand_model} :
    @ErgoDriver.repl_context bm
    -> ergo_declaration
    -> Result.eresult String.string * (@ErgoDriver.repl_context bm)
    := (@ErgoDriver.ergoct_repl_eval_decl bm).

End ErgoCompiler.

