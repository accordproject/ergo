open Datatypes
open ErgoNNRC
open List0
open Misc
open NativeString
open QLib
open TBrandModel
open Version

val java_method_of_body :
  ergo_nnrc_expr -> char list -> nstring -> nstring -> QcertCodeGen.java

val java_method_of_nnrc_function :
  brand_model -> char list -> ergo_nnrc_lambda -> nstring -> nstring ->
  QcertCodeGen.java

val java_methods_of_nnrc_functions :
  brand_model -> (char list * ergo_nnrc_lambda) list -> char list -> nstring
  -> nstring -> QcertCodeGen.java

val java_class_of_nnrc_function_table :
  brand_model -> char list -> ergo_nnrc_function_table -> nstring -> nstring
  -> QcertCodeGen.java

val preamble : nstring -> nstring

val java_of_declaration :
  brand_model -> char list -> ergo_nnrc_declaration -> int -> int -> nstring
  -> nstring -> (QcertCodeGen.java * QcertCodeGen.java_data) * int

val java_of_declarations :
  brand_model -> char list -> ergo_nnrc_declaration list -> int -> int ->
  nstring -> nstring -> QcertCodeGen.java

val nnrc_module_to_java :
  brand_model -> char list -> ergo_nnrc_module -> nstring -> nstring ->
  QcertCodeGen.java

val nnrc_module_to_java_top :
  brand_model -> char list -> ergo_nnrc_module -> QcertCodeGen.java
