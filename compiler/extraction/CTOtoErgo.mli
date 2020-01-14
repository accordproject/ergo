open Ast
open CTO
open Datatypes
open Ergo
open ErgoType
open List0
open Provenance

val cto_type_to_ergo_type : lrcto_type -> lrergo_type

val cto_declaration_desc_to_ergo_type_declaration_desc :
  lrcto_declaration_desc -> lrergo_type_declaration_desc

val cto_declaration_to_ergo_type_declaration :
  lrcto_declaration -> lrergo_type_declaration

val cto_declaration_to_ergo_declaration :
  lrcto_declaration -> lrergo_declaration

val cto_import_to_ergo_declaration :
  provenance import_decl -> lrergo_declaration

val cto_package_to_ergo_module : lrcto_package -> lrergo_module
