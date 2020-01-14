open BinaryOperators
open BrandRelation
open CompLang
open Data
open DataResult
open DataSystem
open DateTimeComponent
open ForeignData
open ForeignType
open ForeignTyping
open ImpEJson
open JSON
open Java
open JavaScriptAst
open ListAdd
open NNRC
open NativeString
open QcertData
open QcertEJson
open QcertModel
open QcertType
open RType
open TBrandContext
open TBrandModel
open UnaryOperators
open Var
open CNNRC

module QcertBackend =
 struct
  type ergo_foreign_ejson = enhanced_ejson

  type ergo_foreign_ejson_runtime_op = enhanced_foreign_ejson_runtime_op

  (** val ergo_foreign_data : foreign_data **)

  let ergo_foreign_data =
    enhanced_foreign_data

  (** val ergo_foreign_type : foreign_type **)

  let ergo_foreign_type =
    enhanced_foreign_type

  module Enhanced = CompEnhanced.Enhanced
 end

module QcertData = QData.QData(QcertBackend)

module QcertOps = QOps.QOps(QcertBackend)

module QcertCodeGen = QCodeGen.QCodeGen(QcertBackend)

module QcertType = QType.QType(QcertBackend)

(** val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list option **)

let zip =
  zip

type qcert_data = QcertData.data

type qcert_type = QcertType.qtype
