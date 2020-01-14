open Ast
open BinaryOperators
open BrandRelation
open CTO
open Data
open DataResult
open Ergo
open ErgoDriver
open ErgoSugar
open ErgoType
open JSON
open Names
open Provenance
open QLib
open RType
open Result0
open TBrandContext
open TBrandModel
open UnaryOperators
open Version

module ErgoCompiler =
 struct
  (** val ergo_version : char list **)

  let ergo_version =
    ergo_version

  module ErgoData = QcertData

  module ErgoOps = QcertOps

  module ErgoCType = QcertType

  (** val javascript_identifier_sanitizer : char list -> char list **)

  let javascript_identifier_sanitizer =
    QcertCodeGen.javascript_identifier_sanitizer

  type location = Provenance.location

  type provenance = Provenance.provenance

  (** val loc_of_provenance : Provenance.provenance -> Provenance.location **)

  let loc_of_provenance =
    loc_of_provenance

  (** val prov_func :
      Provenance.location -> char list -> Provenance.provenance **)

  let prov_func x x0 =
    ProvFunc (x, x0)

  (** val prov_clause :
      Provenance.location -> char list -> Provenance.provenance **)

  let prov_clause x x0 =
    ProvClause (x, x0)

  (** val prov_this_contract :
      Provenance.location -> Provenance.provenance **)

  let prov_this_contract x =
    ProvThisContract x

  (** val prov_this_clause : Provenance.location -> Provenance.provenance **)

  let prov_this_clause x =
    ProvThisClause x

  (** val prov_this_state : Provenance.location -> Provenance.provenance **)

  let prov_this_state x =
    ProvThisState x

  (** val prov_loc : Provenance.location -> Provenance.provenance **)

  let prov_loc x =
    ProvLoc x

  type relative_name = Names.relative_name

  (** val this_name : char list **)

  let this_name =
    this_this

  type eerror = Result0.eerror

  type ewarning = Result0.ewarning

  (** val system_error : provenance -> char list -> eerror **)

  let system_error x x0 =
    ESystemError (x, x0)

  (** val parse_error : provenance -> char list -> eerror **)

  let parse_error x x0 =
    EParseError (x, x0)

  (** val compilation_error : provenance -> char list -> eerror **)

  let compilation_error x x0 =
    ECompilationError (x, x0)

  (** val type_error : provenance -> char list -> eerror **)

  let type_error x x0 =
    ETypeError (x, x0)

  (** val runtime_error : provenance -> char list -> eerror **)

  let runtime_error x x0 =
    ERuntimeError (x, x0)

  type 'a eresult = 'a Result0.eresult

  (** val esuccess : 'a1 -> ewarning list -> 'a1 eresult **)

  let esuccess =
    esuccess

  (** val efailure : eerror -> 'a1 eresult **)

  let efailure =
    efailure

  type result_file = Result0.result_file

  type cto_type = lrcto_type

  type cto_declaration_desc = lrcto_declaration_desc

  type cto_declaration = lrcto_declaration

  type cto_package = lrcto_package

  (** val cto_boolean : provenance -> cto_type **)

  let cto_boolean x =
    CTOBoolean x

  (** val cto_string : provenance -> cto_type **)

  let cto_string x =
    CTOString x

  (** val cto_double : provenance -> cto_type **)

  let cto_double x =
    CTODouble x

  (** val cto_long : provenance -> cto_type **)

  let cto_long x =
    CTOLong x

  (** val cto_integer : provenance -> cto_type **)

  let cto_integer x =
    CTOInteger x

  (** val cto_dateTime : provenance -> cto_type **)

  let cto_dateTime x =
    CTODateTime x

  (** val cto_class_ref :
      Provenance.provenance -> Names.relative_name -> cto_type **)

  let cto_class_ref prov name_ref =
    CTOClassRef (prov, name_ref)

  (** val cto_option :
      Provenance.provenance -> (Provenance.provenance, Names.relative_name)
      CTO.cto_type -> cto_type **)

  let cto_option prov ct =
    CTOOption (prov, ct)

  (** val cto_array :
      Provenance.provenance -> (Provenance.provenance, Names.relative_name)
      CTO.cto_type -> cto_type **)

  let cto_array prov ct =
    CTOArray (prov, ct)

  (** val cto_enum : char list list -> cto_declaration_desc **)

  let cto_enum x =
    CTOEnum x

  (** val cto_transaction :
      bool -> relative_name option -> (char list * cto_type) list ->
      cto_declaration_desc **)

  let cto_transaction x x0 x1 =
    CTOTransaction (x, x0, x1)

  (** val cto_concept :
      bool -> relative_name option -> (char list * cto_type) list ->
      cto_declaration_desc **)

  let cto_concept x x0 x1 =
    CTOConcept (x, x0, x1)

  (** val mk_cto_declaration :
      Provenance.provenance -> char list -> cto_declaration_desc ->
      cto_declaration **)

  let mk_cto_declaration x x0 x1 =
    { cto_declaration_annot = x; cto_declaration_name = x0;
      cto_declaration_type = x1 }

  (** val mk_cto_package :
      Provenance.provenance -> char list -> char list -> char list ->
      Provenance.provenance import_decl list -> cto_declaration list ->
      cto_package **)

  let mk_cto_package x x0 x1 x2 x3 x4 =
    { cto_package_annot = x; cto_package_file = x0; cto_package_prefix = x1;
      cto_package_namespace = x2; cto_package_imports = x3;
      cto_package_declarations = x4 }

  type ergo_type = lrergo_type

  type ergo_type_declaration_desc = lrergo_type_declaration_desc

  type ergo_type_declaration = lrergo_type_declaration

  type laergo_type_declaration = ErgoType.laergo_type_declaration

  (** val ergo_type_any : Provenance.provenance -> ergo_type **)

  let ergo_type_any prov =
    ErgoTypeAny prov

  (** val ergo_type_nothing : Provenance.provenance -> ergo_type **)

  let ergo_type_nothing prov =
    ErgoTypeNothing prov

  (** val ergo_type_unit : Provenance.provenance -> ergo_type **)

  let ergo_type_unit prov =
    ErgoTypeUnit prov

  (** val ergo_type_boolean : Provenance.provenance -> ergo_type **)

  let ergo_type_boolean prov =
    ErgoTypeBoolean prov

  (** val ergo_type_string : Provenance.provenance -> ergo_type **)

  let ergo_type_string prov =
    ErgoTypeString prov

  (** val ergo_type_double : Provenance.provenance -> ergo_type **)

  let ergo_type_double prov =
    ErgoTypeDouble prov

  (** val ergo_type_long : Provenance.provenance -> ergo_type **)

  let ergo_type_long prov =
    ErgoTypeLong prov

  (** val ergo_type_integer : Provenance.provenance -> ergo_type **)

  let ergo_type_integer prov =
    ErgoTypeInteger prov

  (** val ergo_type_dateTime_format : Provenance.provenance -> ergo_type **)

  let ergo_type_dateTime_format prov =
    ErgoTypeDateTimeFormat prov

  (** val ergo_type_dateTime : Provenance.provenance -> ergo_type **)

  let ergo_type_dateTime prov =
    ErgoTypeDateTime prov

  (** val ergo_type_duration : Provenance.provenance -> ergo_type **)

  let ergo_type_duration prov =
    ErgoTypeDuration prov

  (** val ergo_type_period : Provenance.provenance -> ergo_type **)

  let ergo_type_period prov =
    ErgoTypePeriod prov

  (** val ergo_type_class_ref :
      Provenance.provenance -> Names.relative_name -> ergo_type **)

  let ergo_type_class_ref prov relative_name0 =
    ErgoTypeClassRef (prov, relative_name0)

  (** val ergo_type_option :
      Provenance.provenance -> (Provenance.provenance, Names.relative_name)
      ErgoType.ergo_type -> ergo_type **)

  let ergo_type_option prov et =
    ErgoTypeOption (prov, et)

  (** val ergo_type_record :
      Provenance.provenance -> (char list * (Provenance.provenance,
      Names.relative_name) ErgoType.ergo_type) list -> ergo_type **)

  let ergo_type_record prov rec0 =
    ErgoTypeRecord (prov, rec0)

  (** val ergo_type_array :
      Provenance.provenance -> (Provenance.provenance, Names.relative_name)
      ErgoType.ergo_type -> ergo_type **)

  let ergo_type_array prov et =
    ErgoTypeArray (prov, et)

  (** val ergo_type_transaction :
      bool -> relative_name option -> (char list * ergo_type) list ->
      ergo_type_declaration_desc **)

  let ergo_type_transaction x x0 x1 =
    ErgoTypeTransaction (x, x0, x1)

  (** val ergo_type_concept :
      bool -> relative_name option -> (char list * ergo_type) list ->
      ergo_type_declaration_desc **)

  let ergo_type_concept x x0 x1 =
    ErgoTypeConcept (x, x0, x1)

  (** val mk_ergo_type_declaration :
      Provenance.provenance -> char list -> ergo_type_declaration_desc ->
      ergo_type_declaration **)

  let mk_ergo_type_declaration x x0 x1 =
    { type_declaration_annot = x; type_declaration_name = x0;
      type_declaration_type = x1 }

  type ergo_expr = lrergo_expr

  type ergo_stmt = lrergo_stmt

  type ergo_function = lrergo_function

  type ergo_clause = lrergo_clause

  type ergo_declaration = lrergo_declaration

  type ergo_contract = lrergo_contract

  type ergo_module = lrergo_module

  type ergo_input = lrergo_input

  (** val ecasedata :
      Provenance.provenance -> ErgoData.data -> lrergo_pattern **)

  let ecasedata x x0 =
    CaseData (x, x0)

  (** val ecaseenum :
      Provenance.provenance -> (char list option * char list) ->
      lrergo_pattern **)

  let ecaseenum x x0 =
    CaseEnum (x, x0)

  (** val ecasewildcard :
      Provenance.provenance -> Names.relative_name type_annotation ->
      lrergo_pattern **)

  let ecasewildcard x x0 =
    CaseWildcard (x, x0)

  (** val ecaselet :
      Provenance.provenance -> char list -> Names.relative_name
      type_annotation -> lrergo_pattern **)

  let ecaselet x x0 x1 =
    CaseLet (x, x0, x1)

  (** val ecaseletoption :
      Provenance.provenance -> char list -> Names.relative_name
      type_annotation -> lrergo_pattern **)

  let ecaseletoption x x0 x1 =
    CaseLetOption (x, x0, x1)

  (** val ethis_this : Provenance.provenance -> ergo_expr **)

  let ethis_this prov =
    EThis prov

  (** val ethis_contract : Provenance.provenance -> ergo_expr **)

  let ethis_contract prov =
    EThisContract prov

  (** val ethis_clause : Provenance.provenance -> ergo_expr **)

  let ethis_clause prov =
    EThisClause prov

  (** val ethis_state : Provenance.provenance -> ergo_expr **)

  let ethis_state prov =
    EThisState prov

  (** val evar : Provenance.provenance -> Names.relative_name -> ergo_expr **)

  let evar prov v =
    EVar (prov, v)

  (** val econst : Provenance.provenance -> data -> ergo_expr **)

  let econst prov d =
    EConst (prov, d)

  (** val enone : Provenance.provenance -> ergo_expr **)

  let enone prov =
    ENone prov

  (** val esome : Provenance.provenance -> ergo_expr -> ergo_expr **)

  let esome prov x =
    ESome (prov, x)

  (** val earray :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr list -> ergo_expr **)

  let earray prov arr =
    EArray (prov, arr)

  (** val etext :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr list -> ergo_expr **)

  let etext prov el =
    EText (prov, el)

  (** val eunaryoperator :
      Provenance.provenance -> ergo_unary_operator -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let eunaryoperator prov b e =
    EUnaryOperator (prov, b, e)

  (** val ebinaryoperator :
      Provenance.provenance -> ergo_binary_operator ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let ebinaryoperator prov b e1 e2 =
    EBinaryOperator (prov, b, e1, e2)

  (** val eunarybuiltin :
      Provenance.provenance -> QcertOps.Unary.op -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let eunarybuiltin prov u e =
    EUnaryBuiltin (prov, u, e)

  (** val ebinarybuiltin :
      Provenance.provenance -> QcertOps.Binary.op -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr -> ergo_expr **)

  let ebinarybuiltin prov b e1 e2 =
    EBinaryBuiltin (prov, b, e1, e2)

  (** val eif :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr -> ergo_expr **)

  let eif prov e1 e2 e3 =
    EIf (prov, e1, e2, e3)

  (** val elet :
      Provenance.provenance -> char list -> (Provenance.provenance,
      Names.relative_name) ErgoType.ergo_type option -> ergo_expr ->
      ergo_expr -> ergo_expr **)

  let elet prov v t0 e1 e2 =
    ELet (prov, v, t0, e1, e2)

  (** val eprint :
      Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr **)

  let eprint prov e1 e2 =
    EPrint (prov, e1, e2)

  (** val enew :
      Provenance.provenance -> Names.relative_name ->
      (char list * (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr) list -> ergo_expr **)

  let enew prov n rec0 =
    ENew (prov, n, rec0)

  (** val erecord :
      Provenance.provenance -> (char list * (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
      ergo_expr **)

  let erecord prov rec0 =
    ERecord (prov, rec0)

  (** val ecallfun :
      Provenance.provenance -> Names.relative_name -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr list ->
      ergo_expr **)

  let ecallfun prov f el =
    ECallFun (prov, f, el)

  (** val ematch :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ((Provenance.provenance,
      Names.relative_name) ergo_pattern * (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr -> ergo_expr **)

  let ematch prov e0 epl ed =
    EMatch (prov, e0, epl, ed)

  (** val eforeach :
      Provenance.provenance -> (char list * (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr) list ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr option -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let eforeach prov efl ew er =
    EForeach (prov, efl, ew, er)

  (** val eas :
      Provenance.provenance -> char list -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let eas prov f e0 =
    EAs (prov, f, e0)

  (** val opuminusi :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ergo_expr **)

  let opuminusi prov e =
    ebinarybuiltin prov ErgoOps.Binary.Integer.opminusi
      (econst prov (ErgoData.dnat 0)) e

  (** val sreturn :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ergo_stmt **)

  let sreturn prov e =
    SReturn (prov, e)

  (** val efunreturn : provenance -> ergo_expr -> ergo_expr **)

  let efunreturn _ e =
    e

  (** val sthrow :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ergo_stmt **)

  let sthrow prov e =
    SThrow (prov, e)

  (** val scallclause :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> char list ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr list -> ergo_stmt **)

  let scallclause prov e0 c el =
    SCallClause (prov, e0, c, el)

  (** val scallcontract :
      Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_stmt **)

  let scallcontract prov e0 e1 =
    SCallContract (prov, e0, (e1 :: []))

  (** val ssetstate :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_stmt -> ergo_stmt **)

  let ssetstate prov e s =
    SSetState (prov, e, s)

  (** val ssetstatedot :
      Provenance.provenance -> char list -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_stmt -> ergo_stmt **)

  let ssetstatedot prov a e s =
    SSetStateDot (prov, a, e, s)

  (** val semit :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_stmt -> ergo_stmt **)

  let semit prov e s =
    SEmit (prov, e, s)

  (** val slet :
      Provenance.provenance -> char list -> (Provenance.provenance,
      Names.relative_name) ErgoType.ergo_type option -> ergo_expr ->
      ergo_stmt -> ergo_stmt **)

  let slet prov v t0 e1 s2 =
    SLet (prov, v, t0, e1, s2)

  (** val sprint :
      Provenance.provenance -> ergo_expr -> ergo_stmt -> ergo_stmt **)

  let sprint prov e1 s2 =
    SPrint (prov, e1, s2)

  (** val sif :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_stmt ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_stmt -> ergo_stmt **)

  let sif prov e1 s2 s3 =
    SIf (prov, e1, s2, s3)

  (** val senforce :
      Provenance.provenance -> ergo_expr -> ergo_stmt option -> ergo_stmt ->
      ergo_stmt **)

  let senforce prov e1 s2 s3 =
    SEnforce (prov, e1, s2, s3)

  (** val smatch :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_expr -> ((Provenance.provenance,
      Names.relative_name) ergo_pattern * (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_stmt) list ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_stmt -> ergo_stmt **)

  let smatch prov e slp sd =
    SMatch (prov, e, slp, sd)

  (** val eoptionaldot :
      Provenance.provenance -> char list -> ergo_expr -> ergo_expr **)

  let eoptionaldot =
    coq_EOptionalDot

  (** val eoptionaldefault :
      Provenance.provenance -> ergo_expr -> ergo_expr -> ergo_expr **)

  let eoptionaldefault =
    coq_EOptionalDefault

  (** val sreturnempty : Provenance.provenance -> ergo_stmt **)

  let sreturnempty =
    coq_SReturnEmpty

  (** val efunreturnempty : Provenance.provenance -> ergo_expr **)

  let efunreturnempty =
    coq_EFunReturnEmpty

  (** val dnamespace :
      Provenance.provenance -> namespace_name -> ergo_declaration **)

  let dnamespace prov ns =
    DNamespace (prov, ns)

  (** val dimport :
      Provenance.provenance -> Provenance.provenance import_decl ->
      ergo_declaration **)

  let dimport prov id =
    DImport (prov, id)

  (** val dtype :
      Provenance.provenance -> (Provenance.provenance, Names.relative_name)
      ErgoType.ergo_type_declaration -> ergo_declaration **)

  let dtype prov etd =
    DType (prov, etd)

  (** val dstmt :
      Provenance.provenance -> (Provenance.provenance, Provenance.provenance,
      Names.relative_name) Ergo.ergo_stmt -> ergo_declaration **)

  let dstmt prov s =
    DStmt (prov, s)

  (** val dconstant :
      Provenance.provenance -> local_name -> (Provenance.provenance,
      Names.relative_name) ErgoType.ergo_type option ->
      (Provenance.provenance, Provenance.provenance, Names.relative_name)
      Ergo.ergo_expr -> ergo_declaration **)

  let dconstant prov v ta e =
    DConstant (prov, v, ta, e)

  (** val dfunc :
      Provenance.provenance -> local_name -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_function ->
      ergo_declaration **)

  let dfunc prov fn f =
    DFunc (prov, fn, f)

  (** val dcontract :
      Provenance.provenance -> local_name -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_contract ->
      ergo_declaration **)

  let dcontract prov cn c =
    DContract (prov, cn, c)

  (** val dsetcontract :
      Provenance.provenance -> Names.relative_name -> (Provenance.provenance,
      Provenance.provenance, Names.relative_name) Ergo.ergo_expr ->
      ergo_declaration **)

  let dsetcontract prov cn e =
    DSetContract (prov, cn, e)

  (** val ergo_module_to_es6 :
      ergo_input list -> (char list * ergo_expr) list option -> result_file
      Result0.eresult **)

  let ergo_module_to_es6 =
    ergo_module_to_es6_top

  (** val ergo_module_to_java :
      ergo_input list -> (char list * ergo_expr) list option -> result_file
      Result0.eresult **)

  let ergo_module_to_java =
    ergo_module_to_java_top

  (** val ergo_module_to_wasm :
      ergo_input list -> (char list * ergo_expr) list option -> result_file
      Result0.eresult **)

  let ergo_module_to_wasm =
    ergo_module_to_wasm_top

  type ergo_brand_model = ErgoCType.tbrand_model

  (** val ergo_empty_brand_model : ErgoCType.tbrand_model **)

  let ergo_empty_brand_model =
    ErgoCType.tempty_brand_model

  (** val ergo_brand_model_from_inputs :
      ergo_input list -> (ergo_brand_model * laergo_type_declaration list)
      eresult **)

  let ergo_brand_model_from_inputs =
    brand_model_from_inputs

  (** val ergo_refresh_brand_model :
      ergo_brand_model -> repl_context -> (ergo_brand_model * repl_context)
      eresult **)

  let ergo_refresh_brand_model =
    refresh_brand_model

  (** val init_repl_context :
      ergo_brand_model -> ergo_input list -> repl_context Result0.eresult **)

  let init_repl_context =
    init_repl_context

  (** val ergo_repl_eval_decl :
      ergo_brand_model -> repl_context -> ergo_declaration -> char list
      Result0.eresult * repl_context **)

  let ergo_repl_eval_decl =
    ergoct_repl_eval_decl
 end
