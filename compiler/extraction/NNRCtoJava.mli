open Assoc
open BinaryOperators
open BrandRelation
open CoqLibAdd
open Data
open Datatypes
open Digits
open EmitUtil
open EquivDec
open ForeignRuntime
open ForeignToJava
open Java
open List0
open NNRC
open Nat
open NativeString
open StringAdd
open ToString
open UnaryOperators
open Var
open CNNRC
open CNNRCShadow
open CNNRCVars

val unshadow_java : foreign_runtime -> var list -> NNRC.nnrc -> NNRC.nnrc

val mk_java_json_brands : nstring -> brands -> java_json

val mk_java_json_data :
  foreign_runtime -> foreign_to_java -> nstring -> data -> java_json

val uarithToJavaMethod : nat_arith_unary_op -> char list

val float_uarithToJavaMethod : float_arith_unary_op -> char list

val nat_barithToJavaMethod : nat_arith_binary_op -> char list

val float_barithToJavaMethod : float_arith_binary_op -> char list

val float_bcompareToJavaMethod : float_compare_binary_op -> char list

val like_clause_to_java : like_clause -> nstring

val nnrcToJava :
  foreign_runtime -> foreign_to_java -> NNRC.nnrc -> int -> int -> nstring ->
  nstring -> (char list * nstring) list -> (nstring * java_json) * int

val nnrcToJavaunshadow :
  foreign_runtime -> foreign_to_java -> NNRC.nnrc -> int -> int -> nstring ->
  nstring -> var list -> (char list * nstring) list ->
  (nstring * java_json) * int

val makeJavaParams : (char list * nstring) list -> nstring

val closeFreeVars :
  foreign_runtime -> char list -> NNRC.nnrc -> (char list * nstring) list ->
  NNRC.nnrc

val nnrcToJavaFun :
  foreign_runtime -> foreign_to_java -> int -> char list -> NNRC.nnrc ->
  nstring -> nstring -> (char list * nstring) list -> nstring -> nstring
