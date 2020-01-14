open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open Fresh
open Lift
open List0
open NNRS
open NNRSRename
open NNRSVars
open Var

val nnrs_stmt_uncross_shadow_under :
  foreign_runtime -> char list -> nnrs_stmt -> var list -> var list -> var
  list -> nnrs_stmt

val nnrs_uncross_shadow : foreign_runtime -> char list -> nnrs -> nnrs
